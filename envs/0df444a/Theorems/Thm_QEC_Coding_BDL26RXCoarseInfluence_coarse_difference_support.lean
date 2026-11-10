-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_coarse_difference_support
-- name    : QEC.Coding.BDL26RXCoarseInfluence.coarse_difference_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:11:20.42568+00:00
-- url     : https://prove2.me/theorems/e88f4e88-b6e9-4895-aebd-bcd6ed25f53b
-- title:
--   BDL26 RXCoarse Influence: coarse difference support
-- statement:
--   Full lower syndrome difference support; no parent-fibre support is asserted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L155-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L155-L169

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.coarse_difference_support (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) :
    hammingSupport ((rxStepOutput S depth i h sigma).coarse.val +
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val) ⊆
        influence S depth i h q := by sorry
