-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_eq_acceptedBernoulliMass
-- name    : QEC.Distillation.HH18Parameterized.endpointWeight_accepted_eq_acceptedBernoulliMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:03.315751+00:00
-- url     : https://prove2.me/theorems/d405c6c6-5989-42ab-9481-1084aac105ac
-- title:
--   HH18 Parameterized: endpoint Weight accepted eq accepted Bernoulli Mass
-- statement:
--   The actual accepted Born weight is exactly the accepted symbolic Bernoulli
--   mass, with no lower-bound or residual estimate asserted here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L248-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L248-L275

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
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
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.endpointWeight_accepted_eq_acceptedBernoulliMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    endpointWeight h hdegree (noisyResources m w epsilon) .accepted =
      acceptedBernoulliMass w r m epsilon := by sorry
