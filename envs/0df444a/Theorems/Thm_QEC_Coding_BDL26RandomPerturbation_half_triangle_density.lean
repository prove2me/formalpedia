-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_half_triangle_density
-- name    : QEC.Coding.BDL26RandomPerturbation.half_triangle_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:46:00.734175+00:00
-- url     : https://prove2.me/theorems/b135f50b-bf02-4a21-a1ce-f2488a8a3a8b
-- title:
--   BDL26 Random Perturbation: half triangle density
-- statement:
--   Both auxiliary labels are retained: the half-scaled density is at most 250t.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L90-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L90-L108

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.half_triangle_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    (t : ℝ) (hJ : IsBoundedDensityLocalMap P J t) (center : Space) :
    ((familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)).card : ℝ) ≤ 250*t := by sorry
