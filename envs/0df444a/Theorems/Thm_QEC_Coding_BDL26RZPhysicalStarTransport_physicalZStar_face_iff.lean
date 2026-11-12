-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_physicalZStar_face_iff
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.physicalZStar_face_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:18:32.305196+00:00
-- url     : https://prove2.me/theorems/378c368e-5ea2-474b-b541-99844ad9e289
-- title:
--   BDL26 RZPhysical Star Transport: physical ZStar face iff
-- statement:
--   Face existence follows from the original pairing and original X root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L37-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L37-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RZPhysicalStarTransport.physicalZStar_face_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (z : P.Z) (q : P.Q) :
    q ∈ physicalZStar P z ↔ ∃ f : P.Face, ∃ c : Fin 2,
      P.faceZ f=z ∧ P.faceQ f c=q := by sorry
