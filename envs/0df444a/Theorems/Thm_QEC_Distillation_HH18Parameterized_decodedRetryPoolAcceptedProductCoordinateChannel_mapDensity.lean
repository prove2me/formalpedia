-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:02:36.372954+00:00
-- url     : https://prove2.me/theorems/77d7ead7-6b02-4533-83ca-b704784f3748
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Product Coordinate Channel map Density
-- statement:
--   On the genuine accepted product, a named block/port coordinate is the
--   actual selected-port accepted output at that product's physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L69-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L69-L89

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedProductCoordinateChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) (block : Fin required) (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedProductCoordinateChannel
      m w required block port).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by sorry
