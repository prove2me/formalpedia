-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_rootLift_support
-- name    : QEC.Coding.BDL26RZConcreteParity.rootLift_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:40:31.721495+00:00
-- url     : https://prove2.me/theorems/41386470-52fb-4311-aa37-a2ee15c11678
-- title:
--   BDL26 RZConcrete Parity: root Lift support
-- statement:
--   The BDL26 RZConcrete Parity construction uses the root Lift support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L64-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L64-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.rootLift_support (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) (b : BDL26Field) :
    hammingSupport (rootLift P A S z b) ⊆ blockRegion P S z := by sorry
