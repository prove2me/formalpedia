-- Prove2me | Theorems.Thm_UninformedMG_visit_residual_identity
-- name    : UninformedMG.visit_residual_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:23.398361+00:00
-- url     : https://prove2.me/theorems/354315b6-2d1b-4ca5-ad68-9c3c40b2cfa1
-- title:
--   p.19 and Eq. (15) — visit-averaged residuals equal $L^k-\mathrm{Drift}(z^k,q^k,T^k)$, and $\sum P^k(s^k_h=s)\bar{\mathcal J}^k_h=\mathcal J(z^k,q^k,T^k)$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$. For episode $k$ let $T^k_h(s'\mid s,a)=\sum_b\nu^k_h(b\mid s)P_h(s'\mid s,a,b)$, let $d=d^{z^k,q^k,T^k}$ be the visitation (11) started at $s^k_1$, let $P^k=\mathbb P(\cdot\mid F^k)$ and $L^k=V^{\mu^k,\nu^k}_1(s^k_1)/H$. Then:
--
--   1. $T^k\in\mathcal T_{\mathrm{all}}$;
--   2. almost surely $P^k(s^k_h=s)=d_h(s)$ for every step $h$ and state $s$;
--   3. almost surely
--   $$\sum_{h,s}P^k(s^k_h=s)\sum_vq^k_h(v\mid s)\Big(\sum_a\pi^k_h(a\mid s,v)Y^k_{h,s,v,a}-v_h(s)\Big)=L^k-\mathrm{Drift}(z^k,q^k,T^k);$$
--   4. almost surely $\sum_{h,s}P^k(s^k_h=s)\,\bar{\mathcal J}^k_h(s,q^k)=\mathcal J(z^k,q^k,T^k)$.
--
--   This identity turns the per-step bounds of Lemma B.2 into the objective $\Phi$ that the algorithm minimizes, so that Lemma B.6 applies.
--
--   Differences from the source:
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - encoding: the adaptive-opponent protocol of Section 1.1 → an Interaction: lexicographic history filtration, measurability of states, actions, policies, and the conditional step law; reason: this is the protocol's formal content; the natural history filtration is an instance
--   - reading: the sum of the true residuals in Lemma B.2, averaged over state visits; Ek[J^k] ≤ Σ P^k(s^k_h = s) J̄^k_h = 𝒥(z^k,q^k,T^k) → the visit probabilities P^k(s^k_h = s) as weights, with P^k(s^k_h = s) = d_h(s) as its own clause, and the equality part of (15); reason: this is what "averaged over state visits" and the equality in (15) say; Eq. (14) itself is printed for the sketch feedback (8)
--   - encoding: L^k = E^k[Σ_h ℓ^k_h/H] (p.5) → L^k := V^{μ^k,ν^k}_1(s^k_1)/H; reason: the paper uses this identity (p.26); same quantity
--   - encoding: P^k(E) → conditional expectation of the indicator of E given I.filt (k, 0); reason: Lean convention
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), proof of Lemma B.3, p.19 (PDF p.21); Eq. (15), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
open MeasureTheory

namespace UninformedMG

/-- **Visit-averaged residual identity** (proof of Lemma B.3, p.19 = PDF p.21; Eq. (15), p.8 = PDF p.10).
Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

"The actual effective transition kernel `T^k` belongs to `T_all`. By Eq. (12), the sum of the true
residuals in Lemma B.2, averaged over state visits, equals `L^k − Drift(z^k, q^k, T^k)`", and
`∑_{h,s} P^k(s^k_h = s) J̄^k_h(s, q^k) = 𝒥(z^k, q^k, T^k)` (the equality in Eq. (15)). Here
`T^k_h(s'|s,a) = ∑_b ν^k_h(b|s) P_h(s'|s,a,b)`, `L^k = V^{μ^k,ν^k}_1(s^k_1)/H`, `P^k = P(· | F^k)`, and
the visit probabilities are `P^k(s^k_h = s) = d^{z^k,q^k,T^k}_h(s)` started at `s^k_1`.

**Formalization Note.** `F^k` is `I.filt (k, 0)`. `P^k(E)` is the conditional expectation of the
indicator of `E`. Four clauses: `T^k ∈ T_all`; the visit probabilities; the residual identity;
the cost identity (the last two almost surely). -/
theorem visit_residual_identity {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (k : Fin K) :
    (∀ ω, IsKernel G (effKernel G (I.opol k ω))) ∧
    (∀ (h : Fin (H + 1)) (s : G.St h),
      P[{ω | I.st k h ω = s}.indicator (fun _ => (1 : ℝ)) | I.filt (toLex (k, 0))] =ᵐ[P]
        fun ω => visit (grid G K) (R.pi k.castSucc ω) (R.q k ω) (effKernel G (I.opol k ω))
          (I.st k 0 ω) h s) ∧
    (∀ᵐ ω ∂P,
      ∑ h : Fin H, ∑ s, (P[{ω' | I.st k h.castSucc ω' = s}.indicator (fun _ => (1 : ℝ))
          | I.filt (toLex (k, 0))]) ω *
        ∑ v, R.q k ω h s v * (∑ a, R.pi k.castSucc ω h s v a *
            Ytab G (I.opol k ω) ((grid G K).val v) h s a - (grid G K).val v h.castSucc s) =
      value G (I.lpol k ω) (I.opol k ω) 0 (I.st k 0 ω) / (H : ℝ) -
        drift (grid G K) (R.pi k.castSucc ω) (R.q k ω) (effKernel G (I.opol k ω)) (I.st k 0 ω)) ∧
    (∀ᵐ ω ∂P,
      ∑ h : Fin H, ∑ s, (P[{ω' | I.st k h.castSucc ω' = s}.indicator (fun _ => (1 : ℝ))
          | I.filt (toLex (k, 0))]) ω *
        Jbar (grid G K) (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) h s =
      Jcost (grid G K) (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) (effKernel G (I.opol k ω))
        (I.st k 0 ω)) := by sorry

end UninformedMG
