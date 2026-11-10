-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes1
-- name    : QEC.Coding.BDL26AlternatingCochain.nextMap_commutes1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:17:35.452017+00:00
-- url     : https://prove2.me/theorems/e40caaa4-54f6-4cf0-b56a-298b6506e710
-- title:
--   BDL26 Alternating Cochain: next Map commutes1
-- statement:
--   The actual parity-selected step commutes in degrees one and two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L118-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L118-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph

theorem QEC.Coding.BDL26AlternatingCochain.nextMap_commutes1 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary1 (nextState S n C).presentation).comp (nextMap1 S n C) =
      (nextMap2 S n C).comp (tannerCoboundary1 C.presentation) := by sorry
