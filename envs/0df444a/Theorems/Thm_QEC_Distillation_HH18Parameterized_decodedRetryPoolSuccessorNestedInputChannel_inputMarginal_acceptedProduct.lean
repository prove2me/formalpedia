-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:43:51.404201+00:00
-- url     : https://prove2.me/theorems/85810e69-a3a2-43c2-918b-813a546e9181
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Nested Input Channel input Marginal accepted Product
-- statement:
--   Every true branch marginal of the actual joint successor input produced
--   from a genuine accepted-parent product is the literal noisy-resource product
--   for that port's next routed error rate.  The theorem deliberately remains a
--   marginal statement: the joint successor input may be correlated across
--   distinct logical ports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L792-L818
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L792-L818

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    tensorPowerInputMarginal (logicalOutputCount m w)
        ((decodedRetryPoolSuccessorNestedInputChannel
          m w z q stage hstage).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        (decodedRetryPoolLogicalSiteFinEquiv m w port) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by sorry
