-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_mul
-- name    : QEC.Semantics.DensityOperator.entropyTerm_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:57.719214+00:00
-- url     : https://prove2.me/theorems/c5951a3a-e1d4-407a-9d8f-232f79999f6c
-- title:
--   Density Operator: entropy Term mul
-- statement:
--   The base-two entropy term distributes over nonnegative spectral products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L781-L792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L781-L792

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

theorem QEC.Semantics.DensityOperator.entropyTerm_mul (x y : Real) (hx : 0 <= x) (hy : 0 <= y) :
    entropyTerm (x * y) = y * entropyTerm x + x * entropyTerm y := by sorry
