-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_rootLift_apply
-- name    : QEC.Coding.BDL26RZConcreteParity.rootLift_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:18:14.270394+00:00
-- url     : https://prove2.me/theorems/7af81023-86ff-4eb9-ac38-f3f0e3a65645
-- title:
--   BDL26 RZConcrete Parity: root Lift apply
-- statement:
--   The BDL26 RZConcrete Parity construction uses the root Lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L58-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L58-L62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.rootLift_apply (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z w : P.Z) (b : BDL26Field) (v : ZDoubleCylinderVertex P w S) :
    rootLift P A S z b ⟨w,v⟩ =
      if v = rzMap1ZRoot P A w S then (Pi.single z b : Word BDL26Field P.Z) w else 0 := by sorry
