-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_diameter
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.region_diameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:24:55.728022+00:00
-- url     : https://prove2.me/theorems/6e3b540f-22c7-476c-a807-225c20cbb393
-- title:
--   BDL26 Random Physical Locality: region diameter
-- statement:
--   The BDL26 Random Physical Locality construction uses the region diameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L114-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L114-L122

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_diameter

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPhysicalLocality.region_diameter (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (q r s : Physical S n) (hr : r ∈ region S n q) (hs : s ∈ region S n q) :
    dist (J (.q r)) (J (.q s)) ≤ 4 := by sorry
