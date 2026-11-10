-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_radius
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.region_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:24:02.862346+00:00
-- url     : https://prove2.me/theorems/31838cb1-5995-4860-b2f2-87a566ff66ff
-- title:
--   BDL26 Random Physical Locality: region radius
-- statement:
--   The BDL26 Random Physical Locality construction uses the region radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L103-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L103-L112

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.region_radius (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q r : Physical S n) (hr : r ∈ region S n q) : dist (J (.q r)) (J (.q q)) ≤ 2 := by sorry
