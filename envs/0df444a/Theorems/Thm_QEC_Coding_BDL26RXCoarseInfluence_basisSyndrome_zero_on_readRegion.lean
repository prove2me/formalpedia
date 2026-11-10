-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_basisSyndrome_zero_on_readRegion
-- name    : QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_zero_on_readRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:10:55.723667+00:00
-- url     : https://prove2.me/theorems/dea66a72-c45e-4d43-a6e6-07e0b6b762c2
-- title:
--   BDL26 RXCoarse Influence: basis Syndrome zero on read Region
-- statement:
--   The BDL26 RXCoarse Influence construction uses the basis Syndrome zero on read Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L96-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L96-L101

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_zero_on_readRegion (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : basisSyndrome S depth i q p = 0 := by sorry
