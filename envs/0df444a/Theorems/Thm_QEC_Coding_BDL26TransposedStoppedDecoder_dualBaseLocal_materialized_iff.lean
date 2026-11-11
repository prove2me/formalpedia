-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseLocal_materialized_iff
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseLocal_materialized_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:19:21.723968+00:00
-- url     : https://prove2.me/theorems/d291c6e1-b558-4ff7-99d9-e0cab1048f42
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Local materialized iff
-- statement:
--   The local predicate is transported physical support locality, not syndrome support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L133-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L133-L151

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseLocal_materialized_iff (S : OddScale)
    (e : Word BDL26Field (dualPresentation S 2).Q) :
    dualBaseLocal S e = true ↔
      ∃ center : Vertex (transposePresentation (state S 1).presentation),
        ∀ q, wordEquiv (rzDualQ (state S 1).presentation S) e q ≠ 0 →
          rxCorrectionOwner (transposePresentation (state S 1).presentation) S q = center := by sorry
