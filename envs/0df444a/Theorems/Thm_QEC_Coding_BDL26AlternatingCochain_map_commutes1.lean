-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_map_commutes1
-- name    : QEC.Coding.BDL26AlternatingCochain.map_commutes1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:30.459449+00:00
-- url     : https://prove2.me/theorems/4bc4668d-903a-44ed-ba7d-1d8e92f2e50d
-- title:
--   BDL26 Alternating Cochain: map commutes1
-- statement:
--   Every finite actual alternating prefix commutes with the one coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L166-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L166-L171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph

theorem QEC.Coding.BDL26AlternatingCochain.map_commutes1 (S : OddScale) (n : Nat) :
    (tannerCoboundary1 (state S n).presentation).comp (map1 S n) =
      (map2 S n).comp (tannerCoboundary1 (state S 0).presentation) := by sorry
