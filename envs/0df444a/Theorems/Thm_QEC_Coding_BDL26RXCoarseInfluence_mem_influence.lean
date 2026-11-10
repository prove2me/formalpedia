-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_mem_influence
-- name    : QEC.Coding.BDL26RXCoarseInfluence.mem_influence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:10:54.387193+00:00
-- url     : https://prove2.me/theorems/a7caeee2-b9b9-4726-b379-a469ed13fb11
-- title:
--   BDL26 RXCoarse Influence: mem influence
-- statement:
--   The BDL26 RXCoarse Influence construction uses the mem influence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L83-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L83-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.mem_influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc) :
    z ∈ influence S depth i h q ↔
      ∃ p, basisSyndrome S depth i q p ≠ 0 ∧ p ∈ readRegion S depth i h z := by sorry
