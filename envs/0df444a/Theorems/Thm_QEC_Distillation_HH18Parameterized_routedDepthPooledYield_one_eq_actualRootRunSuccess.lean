-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_one_eq_actualRootRunSuccess
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPooledYield_one_eq_actualRootRunSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:07:57.41321+00:00
-- url     : https://prove2.me/theorems/a62a161b-84bf-4563-b480-f35b16a8188b
-- title:
--   HH18 Parameterized: routed Depth Pooled Yield one eq actual Root Run Success
-- statement:
--   At depth one, averaging the identical genuine initial path factors gives
--   exactly that one-level run's success probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L458-L470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L458-L470

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthPooledYield_one_eq_actualRootRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (routedDepthPooledYield h hdegree epsilon hsmall 1 : ℝ) =
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by sorry
