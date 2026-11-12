-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceAcceptedOutput_noisyResources
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedOutput_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:04:33.209445+00:00
-- url     : https://prove2.me/theorems/e45c3063-c715-4315-95e9-475303a62e47
-- title:
--   BH12 Protocol: resource Accepted Output noisy Resources
-- statement:
--   The BH12 Protocol construction uses the resource Accepted Output noisy Resources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1741-L1753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1741-L1753

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedOutput_noisyResources (q : Nat)
    (p : ErrorParameter) (hpos : 0 < endpointWeight q p .accepted) :
    resourceAcceptedOutput q (noisyResources q p)
        (by
          rw [resourceEndpointWeight_noisyResources]
          exact hpos) =
      (decoderChannel q).mapDensity (endpointConditional q p .accepted hpos) := by sorry
