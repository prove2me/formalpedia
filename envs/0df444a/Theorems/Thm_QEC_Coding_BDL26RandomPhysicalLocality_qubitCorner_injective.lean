-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_qubitCorner_injective
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.qubitCorner_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:46:50.05858+00:00
-- url     : https://prove2.me/theorems/3950e638-5831-4c83-adcd-4e5f5eeaea2c
-- title:
--   BDL26 Random Physical Locality: qubit Corner injective
-- statement:
--   The BDL26 Random Physical Locality construction uses the qubit Corner injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L41-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L41-L45

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.qubitCorner_injective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Injective (qubitCorner P A) := by sorry
