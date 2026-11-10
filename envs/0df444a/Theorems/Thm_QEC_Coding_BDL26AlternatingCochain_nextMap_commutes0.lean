-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes0
-- name    : QEC.Coding.BDL26AlternatingCochain.nextMap_commutes0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:58.956179+00:00
-- url     : https://prove2.me/theorems/9f3d827d-9f5d-4ca9-93e4-d6d174aae6b2
-- title:
--   BDL26 Alternating Cochain: next Map commutes0
-- statement:
--   The actual parity-selected step commutes in degrees zero and one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L97-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AlternatingCochain.lean#L97-L115

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26AlternatingCochain
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26DecodingGraph

theorem QEC.Coding.BDL26AlternatingCochain.nextMap_commutes0 (S : OddScale) (n : Nat) (C : ConstructionState) :
    (tannerCoboundary0 (nextState S n C).presentation).comp (nextMap0 S n C) =
      (nextMap1 S n C).comp (tannerCoboundary0 C.presentation) := by sorry
