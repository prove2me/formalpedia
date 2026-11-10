-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_pair_chord
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_pair_chord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:49:38.72196+00:00
-- url     : https://prove2.me/theorems/0926f191-d8e1-4198-b991-b6b193d9ff5e
-- title:
--   BDL26 Random Perturbation: supported pair chord
-- statement:
--   The stronger cap separation gives chord length at least R, hence the source R/6 bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L45-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L45-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.supported_pair_chord (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) : R ≤ ‖p-q‖ := by sorry
