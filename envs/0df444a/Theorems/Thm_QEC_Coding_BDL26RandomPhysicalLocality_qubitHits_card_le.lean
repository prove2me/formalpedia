-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_qubitHits_card_le
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.qubitHits_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:46:25.764842+00:00
-- url     : https://prove2.me/theorems/8ac662ac-6f9c-4013-a4eb-9fe677c88e53
-- title:
--   BDL26 Random Physical Locality: qubit Hits card le
-- statement:
--   The localized injection works for arbitrary regions, including collapsed images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L48-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L48-L62

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.qubitHits_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (J : Vertex P → E) (ball : Set E) :
    (qubitHits P J ball).card ≤ 2 * (familyHits (tannerFaceImage P J) ball).card := by sorry
