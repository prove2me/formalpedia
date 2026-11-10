-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_mem_readRegion
-- name    : QEC.Coding.BDL26RXCoarseInfluence.mem_readRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:04:16.106569+00:00
-- url     : https://prove2.me/theorems/47b0b210-bb52-494c-b4e8-713246cb3203
-- title:
--   BDL26 RXCoarse Influence: mem read Region
-- statement:
--   The BDL26 RXCoarse Influence construction uses the mem read Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L69-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L69-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.mem_readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (z : FamilyZ S depth i.castSucc) (p : FamilyZ S depth i.succ) :
    p ∈ readRegion S depth i h z ↔
      ∃ v ∈ xiIndexSet (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).coarseCenter z) 2,
        p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v := by sorry
