-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_eq_region_sum
-- name    : QEC.Coding.BDL26RZConcreteParity.blockParity_eq_region_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:35:50.217065+00:00
-- url     : https://prove2.me/theorems/05cb76ba-fbda-4af9-8f3d-e1c709f245d9
-- title:
--   BDL26 RZConcrete Parity: block Parity eq region sum
-- statement:
--   The BDL26 RZConcrete Parity construction uses the block Parity eq region sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L43-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L43-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.blockParity_eq_region_sum (P : TannerSquarePresentation) (S : OddScale)
    (r : Word BDL26Field (RZZ P S)) (z : P.Z) :
    blockParity P S r z = ∑ t ∈ blockRegion P S z, r t := by sorry
