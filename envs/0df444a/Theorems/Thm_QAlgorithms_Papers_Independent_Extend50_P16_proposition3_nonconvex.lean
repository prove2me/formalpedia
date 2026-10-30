-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_proposition3_nonconvex
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.proposition3_nonconvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:02:46.520883+00:00
-- url     : https://prove2.me/theorems/c6bd09f5-b290-4e82-aa08-135bf93cf7e4
-- title:
--   Exact PPT cost is not convex
-- statement:
--   Let $\rho_1=\Phi_2$ and $\rho_2=(|00\rangle\langle00|+|11\rangle\langle11|)/2$ be two-qubit density operators, and let $\bar\rho=(\rho_1+\rho_2)/2$. Write $E_{\mathrm{PPT}}$ for the deterministic exact preparation cost under completely PPT-preserving channels: the limit superior of the one-shot cost per copy. These three operators are normalized states, and
--
--   $$
--   E_{\mathrm{PPT}}(\rho_1)=1,\qquad E_{\mathrm{PPT}}(\rho_2)=0,\qquad E_{\mathrm{PPT}}(\bar\rho)=\log_2(3/2)>\tfrac12\bigl(E_{\mathrm{PPT}}(\rho_1)+E_{\mathrm{PPT}}(\rho_2)\bigr).
--   $$
--
--   This explicit strict violation establishes the failure of convexity of the operational cost.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 4, Proposition 3 (No convexity): exact PPT cost

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Proposition 3: strict nonconvexity for the concrete two-qubit
states and their actual average. Costs retain their operational definitions. -/
theorem proposition3_nonconvex :
    IsDensityMatrix convexityFirst ∧ IsDensityMatrix convexitySecond ∧
    IsDensityMatrix convexityAverage ∧
    exactCost convexityFirst = 1 ∧ exactCost convexitySecond = 0 ∧
    exactCost convexityAverage = logTwoReal (3 / 2) ∧
    (1 / 2 : EReal) * (exactCost convexityFirst + exactCost convexitySecond) <
      exactCost convexityAverage := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
