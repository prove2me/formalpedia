-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoFreshParentNextInput_eq_noisyTInvResource
-- name    : QEC.Distillation.HH18Parameterized.depthTwoFreshParentNextInput_eq_noisyTInvResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:49:02.353498+00:00
-- url     : https://prove2.me/theorems/4203cbae-387f-4130-a005-87b6333076c6
-- title:
--   HH18 Parameterized: depth Two Fresh Parent Next Input eq noisy TInv Resource
-- statement:
--   A routed fresh parent source supplies exactly the homogeneous noisy
--   inverse-T resource at the measured rate of its selected logical port.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L178-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L178-L189

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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

theorem QEC.Distillation.HH18Parameterized.depthTwoFreshParentNextInput_eq_noisyTInvResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon source.2 ≤ 1 / 2) :
    depthTwoFreshParentNextInput h hdegree epsilon source =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree epsilon source.2 hhalf) := by sorry
