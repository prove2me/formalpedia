-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxTransport_boundary_z_zero
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxTransport_boundary_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:14:07.377934+00:00
-- url     : https://prove2.me/theorems/e0409b4c-b9db-4ac5-94f6-f7c2fdf13d22
-- title:
--   BDL26 RXDecoder Adapter: rx Transport boundary z zero
-- statement:
--   Transport an actual raw zero Z-boundary using the defining RX successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1077-L1094
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1077-L1094

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open BDL26IndexedDecoder BDL26AlternatingCochain
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open RXCoarseGrainingData

theorem QEC.Coding.BDL26RXDecoderAdapter.rxTransport_boundary_z_zero (h : i.val % 2 = 0)
    (e : Word BDL26Field (RX1 (state S i.val).presentation S))
    (he : ∀ z b, rxCoboundary1 (state S i.val).presentation S e (Sum.inr (z,b)) = 0) :
    ∀ z b, (indexedFamily S depth).coboundary1 i.succ
      (Eq.mpr (congrArg (fun C : ConstructionState => Word BDL26Field C.presentation.Q)
        (stateSuccRX S depth i h)) e)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val = 0 := by sorry
