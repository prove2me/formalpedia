-- Prove2me | Theorems.Thm_UninformedMG_lemma_B_2
-- name    : UninformedMG.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:43:59.442214+00:00
-- url     : https://prove2.me/theorems/02417a1c-1720-430f-b6c1-6308a9c974b1
-- title:
--   Lemma B.2 — one-step bound on $\mathbb E^k_h[\sum_v w^k(v)(M^k_{h,s,v}-1)]$
-- statement:
--   Consider a run of Algorithm 1 on the grid $\mathcal V$ with $0<\lambda\le1/(2S)$. For every episode $k$ and step $h$, with $s=s^k_h$, almost surely
--   $$\mathbb E^k_h\Big[\sum_vw^k(v)\big(M^k_{h,s,v}-1\big)\Big]\le-\lambda\sum_vq^k_h(v\mid s)\Big(\sum_a\pi^k_h(a\mid s,v)Y^k_{h,s,v,a}-v_h(s)\Big)+\lambda^2\bar{\mathcal J}^k_h(s,q^k),$$
--   where $\mathbb E^k_h=\mathbb E[\cdot\mid F^k_h]$, $Y^k_{h,s,v,a}=\sum_b\nu^k_h(b\mid s)[\ell_h(s,a,b)/H+P_hv_{h+1}(s,a,b)]$ and $\bar{\mathcal J}^k_h(s,q)=\bar{\mathcal J}_h(z^k,s,q)$ is the cost (22).
--
--   The right side splits into the true Bellman residuals of the candidates under the mixture, which are controlled by the drift, and the second-order cost, which is controlled by Lemma B.6.
--
--   Differences from the source:
--   - generalization: Algorithm 1 run with the λ of Theorem 2.1, the learner computing q^k from its own observations → any run with 0 < λ ≤ 1/(2S) and any F^k-measurable selection q^k of the argmin in (23); reason: the theorem's λ lies in this range since A + 1 ≥ 1, and every learner selection is an F^k-measurable selection
--   - encoding: the adaptive-opponent protocol of Section 1.1 → an Interaction: lexicographic history filtration, measurability of states, actions, policies, and the conditional step law; reason: this is the protocol's formal content; the natural history filtration is an instance
--   - encoding: E^k_h[·] → Mathlib's conditional expectation given I.filt (k, h); reason: the integrand is bounded and measurable on a run, so it is the conditional expectation
--   - encoding: steps h = 1, …, H+1 and episodes k = 1, …, K → 0-based Lean indices (layer h is step h + 1, Fin.last H the terminal layer); reason: Lean convention; same instances
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Lemma B.2, p.18 (PDF p.20), proof pp.18–19

import Mathlib
import Definitions.Def_UninformedMG_grid
import Definitions.Def_UninformedMG_Run
import Definitions.Def_UninformedMG_potQ
open MeasureTheory

namespace UninformedMG

/-- **Lemma B.2** (p.18 = PDF p.20; proof to p.19). Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…).

For every episode `k` and step `h`, with `s = s^k_h`, almost surely
`E^k_h[∑_v w^k(v)(M^k_{h,s,v} − 1)] ≤ −λ ∑_v q^k_h(v|s)(∑_a π^k_h(a|s,v) Y^k_{h,s,v,a} − v_h(s)) +
λ² J̄^k_h(s, q^k)`, where `E^k_h = E[· | F^k_h]`, `Y^k = Ytab G ν^k`, and `J̄` is Eq. (22).

**Formalization Note.** `F^k_h` is `I.filt (k, h)` (0-based); the conditional expectation is
Mathlib's `condExp`; the integrand is bounded and measurable on a run. -/
theorem lemma_B_2 {H K : ℕ} (hH : 2 ≤ H) (hK : 1 ≤ K) (G : Game H) (A : ℕ)
    (hA : ∀ h, Fintype.card (G.Act h) ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : Interaction G K Ω P)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / (2 * (G.numStates : ℝ)))
    (R : Run (grid G K) lam I) (k : Fin K) (h : Fin H) :
    ∀ᵐ ω ∂P,
      (P[fun ω' => ∑ v, R.w k.castSucc ω' v *
          (Mk (grid G K) lam (R.pi k.castSucc ω') (R.g k ω') h (I.st k h.castSucc ω') v - 1)
          | I.filt (toLex (k, h.castSucc))]) ω ≤
        -lam * ∑ v, R.q k ω h (I.st k h.castSucc ω) v *
            (∑ a, R.pi k.castSucc ω h (I.st k h.castSucc ω) v a *
                Ytab G (I.opol k ω) ((grid G K).val v) h (I.st k h.castSucc ω) a -
              (grid G K).val v h.castSucc (I.st k h.castSucc ω)) +
          lam ^ 2 * Jbar (grid G K) (R.w k.castSucc ω) (R.pi k.castSucc ω) (R.q k ω) h
            (I.st k h.castSucc ω) := by sorry

end UninformedMG
