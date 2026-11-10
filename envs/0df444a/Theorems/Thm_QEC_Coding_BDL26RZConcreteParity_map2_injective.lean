-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_map2_injective
-- name    : QEC.Coding.BDL26RZConcreteParity.map2_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:24:55.303567+00:00
-- url     : https://prove2.me/theorems/c2cce484-b516-44c6-9388-83d3e9fd44b1
-- title:
--   BDL26 RZConcrete Parity: map2 injective
-- statement:
--   The BDL26 RZConcrete Parity construction uses the map2 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L89-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L89-L93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.map2_injective (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) : Function.Injective (map2Coord P A S) := by sorry
