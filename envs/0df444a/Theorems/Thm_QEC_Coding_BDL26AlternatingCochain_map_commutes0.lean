-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_map_commutes0
-- name    : QEC.Coding.BDL26AlternatingCochain.map_commutes0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:11:48.16661+00:00
-- url     : https://prove2.me/theorems/da6e8a50-4a96-4bd2-a31b-09434b2d1beb
-- title:
--   BDL26 Alternating Cochain: map commutes0
-- statement:
--   Every finite actual alternating prefix commutes with the zero coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L158-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L158-L163

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph

theorem QEC.Coding.BDL26AlternatingCochain.map_commutes0 (S : OddScale) (n : Nat) :
    (tannerCoboundary0 (state S n).presentation).comp (map0 S n) =
      (map1 S n).comp (tannerCoboundary0 (state S 0).presentation) := by sorry
