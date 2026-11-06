-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_inner_rankOne_basis_apply
-- name    : QEC.Semantics.DensityOperator.inner_rankOne_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:25.66334+00:00
-- url     : https://prove2.me/theorems/004ee0cd-d239-499c-820a-335695399a99
-- title:
--   Density Operator: inner rank One basis apply
-- statement:
--   The inner-product matrix entry of a rank-one basis operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L343-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L343-L354

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

theorem QEC.Semantics.DensityOperator.inner_rankOne_basis_apply {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (i j r s : Fin (Module.finrank Complex K)) :
    inner Complex (b r) ((InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap (b s)) =
      (if j = s then if r = i then 1 else 0 else 0) := by sorry
