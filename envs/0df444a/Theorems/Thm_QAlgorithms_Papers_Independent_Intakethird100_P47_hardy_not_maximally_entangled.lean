-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_not_maximally_entangled
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_not_maximally_entangled
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:39:15.45101+00:00
-- url     : https://prove2.me/theorems/6193f628-a5c4-4592-b658-4095372bb2ef
-- title:
--   No maximally entangled two-qubit Hardy state
-- statement:
--   For the noncommuting local projective bases (3), let $\rho$ be a positive semidefinite two-qubit matrix of trace one satisfying all four positive-success Hardy conditions (1). Then $\operatorname{Tr}_A\rho\ne I_2/2$. Since every satisfying density is pure, this excludes maximal entanglement in the source two-qubit setting.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II A: no maximally entangled qubit Hardy state [15]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II A, PDF p.3, citing [15]: no maximally entangled two-qubit state satisfies
Hardy's positive-success constraints for the bases (3). Its Bob marginal is not I2/2;
purity of any satisfying density is asserted separately in hardy_no_mixed_state. -/
theorem hardy_not_maximally_entangled (d : HardyParameters)
    (rho : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hrho : IsDensityMatrix rho) (hHardy : HardyConditions (hardyBehavior d rho)) :
    traceLeft rho ≠ (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
