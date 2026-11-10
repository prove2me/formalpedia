-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_scaled_half_triangle_sides
-- name    : QEC.Coding.BDL26RandomPerturbation.scaled_half_triangle_sides
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:56:44.653466+00:00
-- url     : https://prove2.me/theorems/498e95a5-185f-416c-92c4-3c10eedd7c46
-- title:
--   BDL26 Random Perturbation: scaled half triangle sides
-- statement:
--   The approved halfscale preprocessing supplies all three old diameter bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L17-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingGeometry.lean#L17-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.scaled_half_triangle_sides (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) {lambda : ℝ} (hl : 0 ≤ lambda)
    (a : Triangle P) (i j : Fin 3) :
    ‖lambda • ((1/2 : ℝ) • J (triangleVertex P a i))-
      lambda • ((1/2 : ℝ) • J (triangleVertex P a j))‖ ≤ lambda := by sorry
