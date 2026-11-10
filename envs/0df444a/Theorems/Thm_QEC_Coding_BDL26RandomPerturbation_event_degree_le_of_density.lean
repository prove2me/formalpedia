-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_degree_le_of_density
-- name    : QEC.Coding.BDL26RandomPerturbation.event_degree_le_of_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:06:04.440338+00:00
-- url     : https://prove2.me/theorems/10a5ace6-8262-43d7-9eb5-3ce1ad2a7b54
-- title:
--   BDL26 Random Perturbation: event degree le of density
-- statement:
--   Incoming density supplies every local-pool hypothesis used in the degree proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L103-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean#L103-L109

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.event_degree_le_of_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ)
    (t : ℝ) (hJ : BDL26ReplacementEmbedding.IsBoundedDensityLocalMap P J t)
    (hv : BoundedValence P) (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ))
    (e : Event P J K) :
    ((supportGraph (eventSupport P J K)).neighborFinset e).card ≤ 12*56*M^3 := by sorry
