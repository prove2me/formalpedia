-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_conj_spectralPurification
-- name    : QEC.Semantics.DensityOperator.tensorSwap_conj_spectralPurification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:20.158204+00:00
-- url     : https://prove2.me/theorems/d4ea4960-5d00-448f-bdbc-301a906cbf07
-- title:
--   Density Operator: tensor Swap conj spectral Purification
-- statement:
--   The spectral purification density operator is invariant under factor swap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L611-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L611-L616

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

theorem QEC.Semantics.DensityOperator.tensorSwap_conj_spectralPurification (rho : DensityOperator H) :
    (tensorSwap H H).conjDensity (spectralPurification rho) = spectralPurification rho := by sorry
