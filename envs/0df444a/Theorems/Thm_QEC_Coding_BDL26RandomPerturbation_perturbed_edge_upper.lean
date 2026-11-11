-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbed_edge_upper
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbed_edge_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:50:07.865584+00:00
-- url     : https://prove2.me/theorems/dfce5916-e504-4ec4-8498-6e4677b9f8e3
-- title:
--   BDL26 Random Perturbation: perturbed edge upper
-- statement:
--   The BDL26 Random Perturbation construction uses the perturbed edge upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L82-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L82-L90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.perturbed_edge_upper (a b p q : E) {R lambda : ℝ}
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hold : ‖a-b‖ ≤ lambda) :
    ‖(a+p)-(b+q)‖ ≤ 2*R+lambda := by sorry
