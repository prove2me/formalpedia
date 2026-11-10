-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockRegion_disjoint
-- name    : QEC.Coding.BDL26RZConcreteParity.blockRegion_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:19:28.690266+00:00
-- url     : https://prove2.me/theorems/4c92f892-867f-4851-9e97-70aab564c685
-- title:
--   BDL26 RZConcrete Parity: block Region disjoint
-- statement:
--   The BDL26 RZConcrete Parity construction uses the block Region disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L39-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L39-L41

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.blockRegion_disjoint (P : TannerSquarePresentation) (S : OddScale)
    {z w : P.Z} (h : z ≠ w) : Disjoint (blockRegion P S z) (blockRegion P S w) := by sorry
