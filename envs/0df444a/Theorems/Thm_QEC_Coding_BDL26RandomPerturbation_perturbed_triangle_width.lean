-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbed_triangle_width
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbed_triangle_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:49:48.820566+00:00
-- url     : https://prove2.me/theorems/703f4171-d1db-4285-a2bc-4cab72747bcb
-- title:
--   BDL26 Random Perturbation: perturbed triangle width
-- statement:
--   All three opposite segments inherit the same radial lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L93-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L93-L126

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.perturbed_triangle_width (a b c p q s : E) {R lambda : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hs : ‖s‖ = R)
    (hpq : ⟪p,q⟫_ℝ ≤ R^2/4) (hps : ⟪p,s⟫_ℝ ≤ R^2/4)
    (hqs : ⟪q,s⟫_ℝ ≤ R^2/4)
    (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda) (hbc : ‖b-c‖ ≤ lambda) :
    TriangleWidthAtLeast ((b+q)-(a+p)) ((c+s)-(a+p)) (R*(1-1/4)-lambda) := by sorry
