-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_qubit_density_le
-- name    : QEC.Coding.BDL26RandomPhysicalLocality.qubit_density_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:12.320534+00:00
-- url     : https://prove2.me/theorems/b261b571-722f-4773-9779-7a69da09a9ce
-- title:
--   BDL26 Random Physical Locality: qubit density le
-- statement:
--   The BDL26 Random Physical Locality construction uses the qubit density le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L64-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PhysicalLocality.lean#L64-L70

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

theorem QEC.Coding.BDL26RandomPhysicalLocality.qubit_density_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (J : Vertex P → E) {t : ℝ} (hJ : IsBoundedDensityLocalMap P J t) (c : E) :
    ((qubitHits P J (Metric.closedBall c 1)).card : ℝ) ≤ 2*t := by sorry
