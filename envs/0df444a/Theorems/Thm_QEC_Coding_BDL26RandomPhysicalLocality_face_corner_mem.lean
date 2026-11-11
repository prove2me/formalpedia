-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_face_corner_mem
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.face_corner_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:00.907005+00:00
-- url     : https://prove2.me/theorems/f055b7cb-f96a-4a37-bbae-ac7d001eceb5
-- title:
--   BDL26 Random Physical Locality: face corner mem
-- statement:
--   The BDL26 Random Physical Locality construction uses the face corner mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L25-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L25-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPhysicalLocality.face_corner_mem (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (k : Two) : J (.q (P.faceQ f k)) ∈ tannerFaceImage P J f := by sorry
