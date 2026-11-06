-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_bra_comp_ket
-- name    : QEC.Semantics.DensityOperator.bra_comp_ket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:52.049921+00:00
-- url     : https://prove2.me/theorems/99b97006-5e22-4501-a268-cf79e94d00e4
-- title:
--   Density Operator: bra comp ket
-- statement:
--   A normalized bra followed by its ket is the identity on the scalar factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L501-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L501-L511

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

theorem QEC.Semantics.DensityOperator.bra_comp_ket (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (bra psi).comp (ket psi) = 1 := by sorry
