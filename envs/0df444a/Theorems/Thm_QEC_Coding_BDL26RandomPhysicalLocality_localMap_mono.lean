-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_localMap_mono
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.localMap_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:42:36.575698+00:00
-- url     : https://prove2.me/theorems/fa259ffa-70a5-4b55-90b8-15dc4f356077
-- title:
--   BDL26 Random Physical Locality: local Map mono
-- statement:
--   The BDL26 Random Physical Locality construction uses the local Map mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L72-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L72-L75

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.localMap_mono (P : TannerSquarePresentation) (J : Vertex P → E)
    {s t : ℝ} (hJ : IsBoundedDensityLocalMap P J s) (hst : s ≤ t) :
    IsBoundedDensityLocalMap P J t := by sorry
