-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_no_mixed_state
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_no_mixed_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:38:44.332445+00:00
-- url     : https://prove2.me/theorems/8203dd3a-6323-4812-bd90-329cdad3111f
-- title:
--   No genuinely mixed two-qubit Hardy state
-- statement:
--   For the noncommuting local projective bases (3), let $\rho$ be a positive semidefinite two-qubit matrix of trace one satisfying all four Hardy conditions (1), including strictly positive success. Then there is a unit vector $\psi$ with $\rho=|\psi\rangle\langle\psi|$. Thus every such density is pure.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II A: no mixed two-qubit Hardy state [20]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II A, PDF p.3, citing [20]: every two-qubit density satisfying the positive-success
Hardy constraints for the fixed noncommuting bases (3) is pure. The normalized witness
is concluded, so a genuinely mixed state cannot satisfy these conditions. -/
theorem hardy_no_mixed_state (d : HardyParameters)
    (rho : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hrho : IsDensityMatrix rho) (hHardy : HardyConditions (hardyBehavior d rho)) :
    ∃ psi : EuclideanSpace ℂ (Bool × Bool), IsState psi ∧ rho = pureDensity psi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
