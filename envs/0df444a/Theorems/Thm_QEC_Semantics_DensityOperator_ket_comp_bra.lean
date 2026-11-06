-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_ket_comp_bra
-- name    : QEC.Semantics.DensityOperator.ket_comp_bra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:46.653804+00:00
-- url     : https://prove2.me/theorems/7cff51e8-c247-4166-a30c-a5443415455f
-- title:
--   Density Operator: ket comp bra
-- statement:
--   A normalized ket followed by its bra is the actual rank-one density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L494-L497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L494-L497

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

theorem QEC.Semantics.DensityOperator.ket_comp_bra (psi : H) :
    (ket psi).comp (bra psi) = (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry
