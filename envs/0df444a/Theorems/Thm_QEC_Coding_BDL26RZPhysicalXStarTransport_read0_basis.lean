-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_read0_basis
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.read0_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:28:17.121941+00:00
-- url     : https://prove2.me/theorems/cb4ed022-4238-4a62-87e5-028d2976f666
-- title:
--   BDL26 RZPhysical XStar Transport: read0 basis
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the read0 basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L477-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L477-L480

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.read0_basis (x : RZX (Old S depth i) S) :
    read0 S depth i odd (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (upperXChart S depth i odd x))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x := by sorry
