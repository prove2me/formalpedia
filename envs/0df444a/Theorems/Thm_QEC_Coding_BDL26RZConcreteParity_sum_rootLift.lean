-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_sum_rootLift
-- name    : QEC.Coding.BDL26RZConcreteParity.sum_rootLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:18:41.422905+00:00
-- url     : https://prove2.me/theorems/410cc2ed-0b9e-485c-b366-f71323060ab5
-- title:
--   BDL26 RZConcrete Parity: sum root Lift
-- statement:
--   The BDL26 RZConcrete Parity construction uses the sum root Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L106-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L106-L110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.sum_rootLift (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) :
    (∑ z : P.Z, rootLift P A S z (s z)) = map2Coord P A S s := by sorry
