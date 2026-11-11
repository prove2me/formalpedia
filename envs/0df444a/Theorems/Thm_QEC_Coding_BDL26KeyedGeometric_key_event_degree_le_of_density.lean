-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_degree_le_of_density
-- name    : QEC.Coding.BDL26KeyedGeometric.key_event_degree_le_of_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:43:55.420665+00:00
-- url     : https://prove2.me/theorems/06709a4e-1c67-4ef1-9683-e06bd97f4f4e
-- title:
--   BDL26 Keyed Geometric: key event degree le of density
-- statement:
--   Incoming density supplies every local-pool hypothesis used in the degree proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L115-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L115-L122

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.key_event_degree_le_of_density (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K M : ℕ)
    (t : ℝ) (hJ : BDL26ReplacementEmbedding.IsBoundedDensityLocalMap P J t)
    (hv : BoundedValence P) (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ))
    (e : KeyEvent P key hk J K) :
    ((supportGraph (keySupport P key hk J K)).neighborFinset e).card ≤ 12*56*M^3 := by sorry
