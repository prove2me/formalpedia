-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisDephasing_mapDensity_eq_diagonalAResource
-- name    : QEC.Distillation.BK15.NoisyInput.aBasisDephasing_mapDensity_eq_diagonalAResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:59:49.98638+00:00
-- url     : https://prove2.me/theorems/2a27e32c-b0ea-47cc-9feb-3717c0a9ff5f
-- title:
--   Noisy Input: a Basis Dephasing map Density eq diagonal AResource
-- statement:
--   The Noisy Input construction uses the a Basis Dephasing map Density eq diagonal AResource property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L871-L888
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L871-L888

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.NoisyInput.aBasisDephasing_mapDensity_eq_diagonalAResource
    (rho : DensityOperator QubitSpace) (epsilon : BK15Epsilon)
    (hepsilon : epsilon.epsilon = aInputError rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource epsilon := by sorry
