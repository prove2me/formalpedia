-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxX_boundary_z_zero
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxX_boundary_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:15:31.184694+00:00
-- url     : https://prove2.me/theorems/2a2e4abd-0e53-4664-9599-c70ffc1afc6c
-- title:
--   BDL26 RXDecoder Adapter: rx X boundary z zero
-- statement:
--   Actual X correction boundaries have no Z endpoint contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1051-L1065
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1051-L1065

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

theorem QEC.Coding.BDL26RXDecoderAdapter.rxX_boundary_z_zero (h : i.val % 2 = 0)
    (x : (state S i.val).presentation.X)
    (f : Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x)))
    (z : (state S i.val).presentation.Z) (b : Fin 2) :
    (indexedFamily S depth).coboundary1 i.succ
      (extendWordLinear ((rxLx S depth i h).correctionRegion x) f)
      ((rxData S depth i h).induced.zPairEquiv (z,b)).val = 0 := by sorry
