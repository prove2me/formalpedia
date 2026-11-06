-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_rankOne_sum_sum
-- name    : QEC.Semantics.DensityOperator.rankOne_sum_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:36:07.855891+00:00
-- url     : https://prove2.me/theorems/b5b98a5f-d8a1-4cce-b259-ed0a82d86832
-- title:
--   Density Operator: rank One sum sum
-- statement:
--   Rank one is additive in each finite vector argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L135-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L135-L145

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
omit [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.rankOne_sum_sum {ι : Type*} [Fintype ι] (a b : ι → H) :
    (InnerProductSpace.rankOne Complex (∑ i, a i) (∑ j, b j)).toLinearMap =
      ∑ i, ∑ j, (InnerProductSpace.rankOne Complex (a i) (b j)).toLinearMap := by sorry
