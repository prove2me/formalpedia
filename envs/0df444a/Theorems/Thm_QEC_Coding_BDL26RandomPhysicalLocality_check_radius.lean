-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_check_radius
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.check_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:43:10.753541+00:00
-- url     : https://prove2.me/theorems/89585eb7-91f5-478e-9a46-56f49a9c048d
-- title:
--   BDL26 Random Physical Locality: check radius
-- statement:
--   The BDL26 Random Physical Locality construction uses the check radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L83-L89

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.check_radius (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (j : Sum (ZLabel S n) (XLabel S n)) (r : Physical S n)
    (hr : r ∈ checkSupport S n j) : dist (J (.q r)) (checkCenter S n J j) ≤ 1 := by sorry
