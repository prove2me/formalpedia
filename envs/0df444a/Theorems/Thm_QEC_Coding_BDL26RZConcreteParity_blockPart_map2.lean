-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockPart_map2
-- name    : QEC.Coding.BDL26RZConcreteParity.blockPart_map2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:40:56.633171+00:00
-- url     : https://prove2.me/theorems/4108c41a-c831-403c-9f0d-759474ee7f8c
-- title:
--   BDL26 RZConcrete Parity: block Part map2
-- statement:
--   The BDL26 RZConcrete Parity construction uses the block Part map2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L95-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L95-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.blockPart_map2 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) (z : P.Z) :
    blockPart P S z (map2Coord P A S s) = rootLift P A S z (s z) := by sorry
