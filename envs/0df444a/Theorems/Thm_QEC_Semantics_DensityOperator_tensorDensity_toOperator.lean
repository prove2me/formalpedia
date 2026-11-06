-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
-- name    : QEC.Semantics.DensityOperator.tensorDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:35:24.610871+00:00
-- url     : https://prove2.me/theorems/340622c7-ee44-4514-9ad4-86d16f654e68
-- title:
--   Density Operator: tensor Density to Operator
-- statement:
--   The Density Operator construction uses the tensor Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L714-L718
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L714-L718

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

theorem QEC.Semantics.DensityOperator.tensorDensity_toOperator {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).toOperator = TensorProduct.map rho.toOperator sigma.toOperator := by sorry

attribute [defeq] QEC.Semantics.DensityOperator.tensorDensity_toOperator
