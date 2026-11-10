-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_potential_is_map0
-- name    : QEC.Coding.BDL26RXCohomology.potential_is_map0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:20:20.175209+00:00
-- url     : https://prove2.me/theorems/ae50d76d-c2e4-45f9-bce0-abcbf71b93d0
-- title:
--   BDL26 RXCohomology: potential is map0
-- statement:
--   Zero X derivative forces the entire global degree-zero potential to be
--   an actual constant CX lift, on both copies and every vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L122-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L122-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.potential_is_map0 (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (f : Word Field (RX0 P S))
    (hf : ∀ x e, rxCoboundary0 P S f (Sum.inl ⟨x,e⟩) = 0) :
    ∃ old : Word Field P.X, rxMap0Coord P S old = f := by sorry
