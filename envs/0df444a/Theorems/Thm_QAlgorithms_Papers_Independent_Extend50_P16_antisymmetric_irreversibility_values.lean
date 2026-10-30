-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_antisymmetric_irreversibility_values
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.antisymmetric_irreversibility_values
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:07:15.562703+00:00
-- url     : https://prove2.me/theorems/f493bf8c-c0c2-4771-8897-1197c3d29765
-- title:
--   Rank-two antisymmetric state and strict prior-bound gaps
-- statement:
--   On two qutrits, set $|v_1\rangle=(|01\rangle-|10\rangle)/\sqrt2$, $|v_2\rangle=(|02\rangle-|20\rangle)/\sqrt2$, and $\rho_v=(|v_1\rangle\langle v_1|+|v_2\rangle\langle v_2|)/2$. This is a normalized state. Let $R_{\max}(\rho)=\log_2\inf_{X\succeq\rho}\|T_B(X)\|_1$ be the max-Rains quantity, $E_N$ logarithmic negativity, and $Z(\rho)=\|T_B(\rho)\|_1+d_A d_B\max\{0,-\lambda_{\min}(T_B(|T_B(\rho)|))\}$ the prior upper-bound quantity. Then
--
--   $$
--   R_{\max}(\rho_v)=E_N(\rho_v)=\log_2(1+1/\sqrt2)
--   <E_{\mathrm{PPT}}(\rho_v)=E_\kappa(\rho_v)=1
--   <\log_2 Z(\rho_v)=\log_2\!\left(1+\frac{13}{4\sqrt2}\right).
--   $$
--
--   Both the older lower and upper bounds on exact PPT cost are therefore strict for this state.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 22, Unnumbered main result: rank-two antisymmetric example

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.22, Appendix E (S1)-(S6): all values and strict comparisons
for the fixed antisymmetric state, including the independent prior bounds. -/
theorem antisymmetric_irreversibility_values :
    IsDensityMatrix rankTwoAntisymmetricState ∧
    maxRains rankTwoAntisymmetricState = bipartiteLogNegativity rankTwoAntisymmetricState ∧
    bipartiteLogNegativity rankTwoAntisymmetricState = logTwoReal (1 + 1 / Real.sqrt 2) ∧
    bipartiteLogNegativity rankTwoAntisymmetricState < exactCost rankTwoAntisymmetricState ∧
    exactCost rankTwoAntisymmetricState = kappaEntanglement rankTwoAntisymmetricState ∧
    kappaEntanglement rankTwoAntisymmetricState = 1 ∧
    kappaEntanglement rankTwoAntisymmetricState < logTwoReal (priorUpperBound rankTwoAntisymmetricState) ∧
    logTwoReal (priorUpperBound rankTwoAntisymmetricState) =
      logTwoReal (1 + 13 / (4 * Real.sqrt 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
