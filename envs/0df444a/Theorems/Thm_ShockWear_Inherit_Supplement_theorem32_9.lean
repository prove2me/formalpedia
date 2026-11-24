-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem32_9
-- name    : ShockWear.Inherit.Supplement.theorem32_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:50:30.244374+00:00
-- url     : https://prove2.me/theorems/8b77ec33-65d8-4002-b87a-b8e8330f6e49
-- title:
--   Theorem 3.2 (3.9) — Increasing normalized discrete tails give IMRL
-- statement:
--   Let $\lambda>0$ and $1\ge\bar P_0\ge\bar P_1\ge\cdots\ge0$. For $k\ge0$ let $T_k=\sum_{j=k}^\infty\bar P_j\in[0,\infty]$. If $T_k/\bar P_k$ increases on the indices where $\bar P_k>0$, the Poisson shock survival $\bar H$ has increasing mean residual life:
--
--   $$
--   \frac{\int_0^\infty\bar H(x+s)\,dx}{\bar H(s)}
--   \le
--   \frac{\int_0^\infty\bar H(x+t)\,dx}{\bar H(t)}
--   \quad(0\le s\le t,\ \bar H(s),\bar H(t)>0).
--   $$
--
--   This transfers a discrete residual-tail property to continuous-time residual life, including infinite residual means.
--
--   **Formalization Note** The paper states the normalized sums and residual integrals; we state both as extended nonnegative quantities, with division restricted to positive denominators. There is no summability or finite-mean assumption.
--
--   Differences from the source:
--   - encoding: shock survival probabilities and Poisson rate → explicit λ>0, nonnegative antitone P with P₀≤1; reason: these are the probability assumptions in (1.1)–(2.2); P₀<1 retains the mass at the origin
--   - encoding: possibly infinite normalized tail sums and residual integrals → ENNReal sums and the published extended residual integral on positive denominators; reason: infinite means remain infinite; real tsum and non-integrable Bochner defaults are avoided
--   - generalization: H is a proper life distribution, implicitly Pₖ→0 → the analytic class assertion also allows defective shock survivals; reason: bounded nonnegative coefficients still give convergent Poisson series and the same shape conclusion; every proper source law is included
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 634, Theorem 3.2 (3.9); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

namespace ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem32_9 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (htail : MonotoneOn
      (fun k => (∑' j, ENNReal.ofReal (P (j + k))) / ENNReal.ofReal (P k))
      {k | 0 < P k}) :
    IsIMRL (ShockWear.CumDamage.shockSurv lam P) := by sorry

end ShockWear.Inherit.Supplement
