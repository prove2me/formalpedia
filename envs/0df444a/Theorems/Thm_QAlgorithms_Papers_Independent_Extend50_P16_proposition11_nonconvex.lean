-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_proposition11_nonconvex
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.proposition11_nonconvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:05:27.814249+00:00
-- url     : https://prove2.me/theorems/b9947db9-af95-4485-9a44-265bdbdb685a
-- title:
--   Kappa-entanglement is not convex
-- statement:
--   Let $\rho_1=\Phi_2$, $\rho_2=(|00\rangle\langle00|+|11\rangle\langle11|)/2$, and $\bar\rho=(\rho_1+\rho_2)/2$. These are normalized two-qubit states. Write $E_N(\rho)=\log_2\|T_B(\rho)\|_1$. Their values are
--
--   $$
--   E_\kappa(\rho_1)=E_N(\rho_1)=1,\qquad E_\kappa(\rho_2)=E_N(\rho_2)=0,\qquad E_\kappa(\bar\rho)=E_N(\bar\rho)=\log_2(3/2)>\tfrac12\bigl(E_\kappa(\rho_1)+E_\kappa(\rho_2)\bigr).
--   $$
--
--   This concrete violation proves that kappa-entanglement is not convex; no reverse Jensen inequality for arbitrary states is asserted.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 20, Proposition 11 (No convexity): kappa-entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.20-21, Proposition 11, (S84)-(S87): actual strict Jensen
violation, with all three evaluated κ and logarithmic-negativity values. -/
theorem proposition11_nonconvex :
    IsDensityMatrix convexityFirst ∧ IsDensityMatrix convexitySecond ∧
    IsDensityMatrix convexityAverage ∧
    kappaEntanglement convexityFirst = 1 ∧ bipartiteLogNegativity convexityFirst = 1 ∧
    kappaEntanglement convexitySecond = 0 ∧ bipartiteLogNegativity convexitySecond = 0 ∧
    kappaEntanglement convexityAverage = logTwoReal (3 / 2) ∧
    bipartiteLogNegativity convexityAverage = logTwoReal (3 / 2) ∧
    (1 / 2 : EReal) * (kappaEntanglement convexityFirst + kappaEntanglement convexitySecond) <
      kappaEntanglement convexityAverage := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
