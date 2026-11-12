-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceDecodedRun_acceptedOutput_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.resourceDecodedRun_acceptedOutput_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:18:21.50403+00:00
-- url     : https://prove2.me/theorems/2c02696c-1dab-4004-93c6-fe72ffd0034f
-- title:
--   HH18 Parameterized: resource Decoded Run accepted Output noisy Resources
-- statement:
--   For actual noisy resources, the accepted decoded output is the decoder
--   applied to the real positive conditional endpoint, never its fallback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/NormalizedRun.lean#L188-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/NormalizedRun.lean#L188-L197

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_pos

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instNormalizedRunClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.resourceDecodedRun_acceptedOutput_noisyResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput =
      (decoderChannel h).mapDensity
        (endpointConditional h hdegree (noisyResources m w epsilon) .accepted
          (endpointWeight_accepted_pos h hdegree epsilon)) := by sorry
