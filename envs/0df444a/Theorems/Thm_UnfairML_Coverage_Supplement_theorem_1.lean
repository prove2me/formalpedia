-- Prove2me | Theorems.Thm_UnfairML_Coverage_Supplement_theorem_1
-- name    : UnfairML.Coverage.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:36:12.622861+00:00
-- url     : https://prove2.me/theorems/760c31c0-f7dd-40c4-9258-0262000e6585
-- title:
--   Theorem 1 (corrected: positive utilities) — ET learning effort is at least EO effort in every loss regime
-- statement:
--   Consider the two unit populations, uniform score distributions and payoff parameters of §3.1, with $\alpha,\beta>0$, $0<d_r<d_p<1$, $\alpha_r\le\beta_r$ and $0<\gamma_p<\gamma_r$. Let $\tau$ be any convex nondecreasing learning cost on $[0,1/(2\gamma_r)]$. Let $(c^{ET},s^{ET})$ attain the global ET maximum of profit (1), and let $(c_p^{EO},c_r^{EO},s^{EO})$ attain the global EO maximum under constraint (6). Thresholds lie in $[0,1]$. Then
--   $$s^{ET}\ge s^{EO}.$$
--   The comparison includes low, medium and large expected protected-group losses. No low-loss, rational-cost, interior-solution or uniqueness assumption is imposed. It compares optimal policies, rather than derivatives evaluated at a selected effort.
--
--   Differences from the source:
--   - correction: Table 1 calls α and β utility and dis-utility without explicitly imposing positivity → α>0 and β>0 through the published Standing predicate; reason: the economic utility/loss interpretation and the brief require positive primitives; cases α≤0 or β≤0 are excluded
--   - reading: §3.1 uses the half-open effort interval → the closed interval [0,1/(2γr)] of Appendix A p. 43; reason: Appendix A specifies this boundary convention and it retains endpoint optima
--   - encoding: threshold decisions have their feasible score ranges → thresholds lie in [0,1] and global optimality ranges over the full feasible box; reason: these are the admissible probability thresholds of (1), not additional stationarity assumptions
--   - reading: τ is convex increasing → ConvexOn and MonotoneOn on the admissible effort interval; reason: increasing is read as nondecreasing, with no differentiability or strict-concavity requirement
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 18, Theorem 1; pp. 10–17; pp. 43, 45–49, Appendices A–B

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_CostModel

namespace UnfairML.Coverage.Supplement

/-- Theorem 1, p. 18, including the medium- and large-loss regimes of Appendix B. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (τ : ℝ → ℝ)
    (hτ : IsLearningCost P τ)
    (cET sET : ℝ) (hET : IsOptETWithCost P τ cET sET)
    (cpEO crEO sEO : ℝ) (hEO : IsOptEOWithCost P τ cpEO crEO sEO) :
    sEO ≤ sET := by sorry

end UnfairML.Coverage.Supplement
