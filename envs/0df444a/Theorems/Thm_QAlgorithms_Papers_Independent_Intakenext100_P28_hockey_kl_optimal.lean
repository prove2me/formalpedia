-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_kl_optimal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_kl_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:46:15.517404+00:00
-- url     : https://prove2.me/theorems/2207f44c-c040-4739-9b73-1452a8c9735f
-- title:
--   Theorem 33: For every gamma>1, sup E_gamma/D=c_gamma=(t_gamma-gamma)/r(t_gamma), t_gamma=-gamma W_minus1(-gamma^{-1}e^{-1/gamma})
-- statement:
--   For every $\gamma>1$, let $t_\gamma$ be the unique root larger than $\gamma$ of $\gamma\ln t=t-1$. Equivalently $t_\gamma=-\gamma W_{-1}(-\gamma^{-1}e^{-1/\gamma})$, using the secondary real Lambert branch. Then
--
--   $$\sup_{P\ll Q,\ P\ne Q}\frac{E_\gamma(P\|Q)}{D(P\|Q)}
--   =c_\gamma=\frac{t_\gamma-\gamma}{r(t_\gamma)}.$$
--
--   The formal statement asserts the root characterization and the least universal multiplicative coefficient across all probability spaces. The coefficient depends on the logarithm base but not on the input pair.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 61, Theorem 33

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 33: For every gamma>1, sup E_gamma/D=c_gamma=(t_gamma-gamma)/r(t_gamma), t_gamma=-gamma W_minus1(-gamma^{-1}e^{-1/gamma}). Sason--Verdu, arXiv:1508.00335v7, PDF p.61.  -/
theorem hockey_kl_optimal
    (b : LogBase) (g : ℝ) (hg : 1 < g) :
    g < tGamma g ∧ g * Real.log (tGamma g) = tGamma g - 1 ∧
    (∀ t : ℝ, g < t → g * Real.log t = t - 1 → t = tGamma g) ∧
    Sharp (hockey g) (kl b) acPairs (ENNReal.ofReal (hockeyKLConstant b g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
