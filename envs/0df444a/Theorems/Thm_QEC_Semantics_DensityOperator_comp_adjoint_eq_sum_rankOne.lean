-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_comp_adjoint_eq_sum_rankOne
-- name    : QEC.Semantics.DensityOperator.comp_adjoint_eq_sum_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:37:49.615812+00:00
-- url     : https://prove2.me/theorems/19cbbc8b-0dbe-424d-a3e4-9202b8153c6e
-- title:
--   Density Operator: comp adjoint eq sum rank One
-- statement:
--   A finite Gram operator is the sum of the rank-one columns in an orthonormal basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L272-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L272-L285

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.comp_adjoint_eq_sum_rankOne {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (A : K →ₗ[Complex] H) :
    A.comp (LinearMap.adjoint A) = ∑ j,
      (InnerProductSpace.rankOne Complex (A (b j)) (A (b j))).toLinearMap := by sorry
