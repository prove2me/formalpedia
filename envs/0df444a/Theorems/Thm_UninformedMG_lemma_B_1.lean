-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_1
-- name    : UninformedMG.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:47.366193+00:00
-- url     : https://prove2.me/theorems/1f6b19ec-6061-4806-b4c3-1b05d381d7e6
-- title:
--   Lemma B.1 — OMD identity (26) and the bound (27) on $Q^k$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$ of Eq. (19). At every outcome and for every episode $k$:
--
--   1. the iterates stay strictly positive: $w^j(v)>0$ and $\pi^j_h(a\mid s,v)>0$ for all $j=1,\dots,K+1$;
--   2. for every $z\in\mathcal Z$,
--   $$D_{\mathcal H_{\mathrm{res}}}(z\|z^{k+1})-D_{\mathcal H_{\mathrm{res}}}(z\|z^k)=H\log Q^k+\lambda\langle z,g^k\rangle;\tag{26}$$
--   3. $$Q^k\le1+\frac1H\sum_{h=1}^H\sum_vw^k(v)\big(M^k_{h,s^k_h,v}-1\big).\tag{27}$$
--
--   Here $M^k_{h,s,v}=\sum_a\pi^k_h(a\mid s,v)e^{-\lambda g^k_{h,s,v,a}}$ and $Q^k=\sum_vw^k(v)\big(\prod_{h,s}M^k_{h,s,v}\big)^{1/H}$.
--
--   The identity telescopes over episodes in the proof of Lemma B.3, and (27) converts $Q^k$ into the per-step quantities that Lemma B.2 controls.
--
--   Differences from the source:
--   - encoding: z ∈ 𝒵 → the pair (w, π) of Eq. (4); reason: every z ∈ 𝒵 is w·π and every quantity used is unchanged by π at w(v) = 0
--   - generalization: the identity (26) and the bound (27) → also the strict positivity of every iterate; reason: the proof states that the updates preserve positivity (p.17); dropping the clause gives the printed lemma
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - encoding: (∏ M)^{1/H} → Real.rpow with exponent H⁻¹; reason: M > 0 on a run; same values
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.1, p.17 (PDF p.19), proof pp.17–18

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
open MeasureTheory

namespace UninformedMG

/-- **Lemma B.1** (p.17 = PDF p.19; proof to p.18). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

On every outcome of a run of Algorithm 1: the iterates stay strictly positive ("the displayed
updates … preserve positivity"); for every `z ∈ Z` and every episode `k`,
`D_{ℋres}(z ‖ z^{k+1}) − D_{ℋres}(z ‖ z^k) = H log Q^k + λ⟨z, g^k⟩` (26); and
`Q^k ≤ 1 + H⁻¹ ∑_{h=1}^H ∑_v w^k(v)(M^k_{h,s^k_h,v} − 1)` (27).

**Formalization Note.** Lean iterate `k.castSucc` is `z^k`, `k.succ` is `z^{k+1}`; `z = wπ` ranges over
all pairs (`IsJoint`). `Q^k` is `potQ` with `g^k = R.g k ω`. Stated pointwise in `ω`. -/
theorem lemma_B_1 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (ω : Ω) (k : Fin K) :
    (∀ (j : Fin (K + 1)) v, 0 < R.w j ω v) ∧ (∀ (j : Fin (K + 1)) h s v a, 0 < R.pi j ω h s v a) ∧
    (∀ (w : (grid G K).C → ℝ) (π : CPolicy (grid G K)), IsJoint (grid G K) w π →
      divRes (grid G K) w π (R.w k.succ ω) (R.pi k.succ ω) -
          divRes (grid G K) w π (R.w k.castSucc ω) (R.pi k.castSucc ω) =
        (H : ℝ) * Real.log (potQ (grid G K) lam (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.g k ω)) +
          lam * pairing (grid G K) w π (R.g k ω)) ∧
    potQ (grid G K) lam (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.g k ω) ≤
      1 + (H : ℝ)⁻¹ * ∑ h : Fin H, ∑ v, R.w k.castSucc ω v *
        (Mk (grid G K) lam (R.pi k.castSucc ω) (R.g k ω) h (I.st k h.castSucc ω) v - 1) := by sorry

end UninformedMG
