-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_half_triangle_hit
-- name    : QEC.Coding.BDL26RandomPerturbation.half_triangle_hit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:45:21.925833+00:00
-- url     : https://prove2.me/theorems/7ec8bc5f-fd2d-455d-8db9-de841254195d
-- title:
--   BDL26 Random Perturbation: half triangle hit
-- statement:
--   Half scaling transfers a triangle hit to the original radius-two square hit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L71-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Density.lean#L71-L87

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Density
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.half_triangle_hit (P : TannerSquarePresentation) (J : Vertex P → Space)
    (center : Space) (t : Triangle P)
    (ht : t ∈ familyHits (oldTriangleImage P (fun v => (1/2 : ℝ) • J v))
      (Metric.closedBall center 1)) :
    t.1 ∈ familyHits (tannerFaceImage P J) (Metric.closedBall ((2 : ℝ) • center) 2) := by sorry
