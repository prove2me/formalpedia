-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbed_edge_lower
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbed_edge_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:50:49.932985+00:00
-- url     : https://prove2.me/theorems/7d566208-6665-4ba0-b7ee-24f16590318d
-- title:
--   BDL26 Random Perturbation: perturbed edge lower
-- statement:
--   Adding a diameter-lambda original edge preserves the chord lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L74-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L74-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.perturbed_edge_lower (a b p q : E) {R lambda : ℝ}
    (hchord : R ≤ ‖p-q‖) (hold : ‖a-b‖ ≤ lambda) :
    R-lambda ≤ ‖(a+p)-(b+q)‖ := by sorry
