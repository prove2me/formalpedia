-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_half_triangle_sides
-- name    : QEC.Coding.BDL26RandomPerturbation.half_triangle_sides
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:46:08.960863+00:00
-- url     : https://prove2.me/theorems/d3be95a1-7365-48b2-aa6b-181b1783a705
-- title:
--   BDL26 Random Perturbation: half triangle sides
-- statement:
--   Half scaling controls the diagonal as well as the two Tanner edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L111-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L111-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.half_triangle_sides (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (a : Triangle P) (i j : Fin 3) :
    ‖(1/2 : ℝ) • J (triangleVertex P a i)-(1/2 : ℝ) • J (triangleVertex P a j)‖ ≤ 1 := by sorry
