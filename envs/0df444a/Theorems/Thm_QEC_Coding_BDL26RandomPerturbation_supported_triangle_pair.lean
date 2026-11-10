-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_triangle_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.supported_triangle_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:53:44.409272+00:00
-- url     : https://prove2.me/theorems/0026179b-89b2-4fe3-a2b0-866e7f4ef7ed
-- title:
--   BDL26 Random Perturbation: supported triangle pair
-- statement:
--   The BDL26 Random Perturbation construction uses the supported triangle pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L25-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L25-L36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.supported_triangle_pair (P : TannerSquarePresentation) {R θ : ℝ}
    (hR : 0 < R) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) (p : Vertex P → Space)
    (hp : ∀ v, p v ∈ displacementCap R (vertexAxis P v) (Real.cos θ))
    (a : Triangle P) {i j : Fin 3} (hij : i ≠ j) :
    R ≤ ‖p (triangleVertex P a i)-p (triangleVertex P a j)‖ ∧
      ⟪p (triangleVertex P a i),p (triangleVertex P a j)⟫_ℝ ≤ R^2/4 := by sorry
