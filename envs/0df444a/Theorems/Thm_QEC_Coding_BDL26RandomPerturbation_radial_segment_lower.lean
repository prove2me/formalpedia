-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_radial_segment_lower
-- name    : QEC.Coding.BDL26RandomPerturbation.radial_segment_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:47:54.836551+00:00
-- url     : https://prove2.me/theorems/3e48d370-51ab-45ac-83ca-fdf196bd4019
-- title:
--   BDL26 Random Perturbation: radial segment lower
-- statement:
--   A radial supporting functional separates a vertex from every opposite convex combination.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L62-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L62-L72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26RandomPerturbation.radial_segment_lower (p q s : E) {R c t : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hpq : ⟪p, q⟫_ℝ ≤ R ^ 2 * c)
    (hps : ⟪p, s⟫_ℝ ≤ R ^ 2 * c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R * (1 - c) ≤ ‖p - ((1 - t) • q + t • s)‖ := by sorry
