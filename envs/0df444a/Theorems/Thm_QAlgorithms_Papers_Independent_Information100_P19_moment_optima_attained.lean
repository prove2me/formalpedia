-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_moment_optima_attained
-- name    : QAlgorithms.Papers.Independent.Information100.P19.moment_optima_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:56:24.882388+00:00
-- url     : https://prove2.me/theorems/e1dcd1ad-e15d-4538-8cef-64e8d0bd1f6b
-- title:
--   Equations (17) and the Hausdorff SDP: attainment on feasible data
-- statement:
--   Let $m\ge1$ and $r\in\mathbb R_{\ge0}^{m}$. If $r_1\le1$ and a finite vector $s\in[0,1]^N$ realizes $\sum_i s_i^{2k}=r_k$ for $k=1,\ldots,m$, then such a vector attains the discrete optimum: $$\alpha(r)=\sum_i s_i.$$ If the continuous problem is feasible, there is a finite positive Borel measure $\mu$ supported on $[0,1]$ with the prescribed even moments attaining $$\alpha_c(r)=\int x\,d\mu(x),$$ and a feasible Hausdorff moment sequence attaining the SDP objective $y_1$. No probability normalization or dimension bound is imposed.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 31, §5.1, Eq.(17) and the minimum formulations on pp.32–33

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Equations (17) and the Hausdorff SDP, PDF pp.31–33, use minima.
For feasible data their infimum interfaces attain the objective. The discrete
clause retains the standing first-moment bound; measures have free finite mass. -/
theorem moment_optima_attained (m : ℕ) (hm : 1 ≤ m) (r : Fin m → ℝ)
    (hr : ∀ k, 0 ≤ r k) :
    (r ⟨0, hm⟩ ≤ 1 →
      (∃ N : ℕ, ∃ s : Fin N → ℝ, discreteFeasible r s) →
      ∃ N : ℕ, ∃ s : Fin N → ℝ, discreteFeasible r s ∧
        alpha r = ENNReal.ofReal (∑ i, s i)) ∧
    ((∃ μ : Measure ℝ, continuousFeasible r μ) →
      (∃ μ : Measure ℝ, continuousFeasible r μ ∧
        alphaC r = ENNReal.ofReal (∫ x, x ∂μ)) ∧
      (∃ y : ℕ → ℝ, sdpFeasible r y ∧
        sdpValue r = ENNReal.ofReal (y 1))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
