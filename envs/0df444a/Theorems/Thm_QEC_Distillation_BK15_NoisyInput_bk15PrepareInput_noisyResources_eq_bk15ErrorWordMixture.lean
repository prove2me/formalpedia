-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
-- name    : QEC.Distillation.BK15.NoisyInput.bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:08:03.587204+00:00
-- url     : https://prove2.me/theorems/c6da92a5-9f69-4631-b6a0-7a7f118e7e62
-- title:
--   Noisy Input: bk15 Prepare Input noisy Resources eq bk15 Error Word Mixture
-- statement:
--   The physical fifteen-site noisy product is exactly the explicit flat
--   `2^15`-term error-word mixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L1390-L1395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L1390-L1395

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

theorem QEC.Distillation.BK15.NoisyInput.bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
    (epsilon : BK15Epsilon) :
    bk15PrepareInput (bk15NoisyResources epsilon) = bk15ErrorWordMixture epsilon := by sorry
