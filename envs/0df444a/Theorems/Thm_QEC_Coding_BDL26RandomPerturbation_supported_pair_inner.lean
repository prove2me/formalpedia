-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_pair_inner
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_pair_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:43:54.727993+00:00
-- url     : https://prove2.me/theorems/23c86a23-846e-4072-8991-85044e14c76c
-- title:
--   BDL26 Random Perturbation: supported pair inner
-- statement:
--   Actual ambient displacement laws inherit the orthogonal unit-cap estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L30-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L30-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.supported_pair_inner (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) :
    ⟪p,q⟫_ℝ ≤ R^2 / 4 := by sorry
