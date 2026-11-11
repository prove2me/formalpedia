-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_common_hits_anchor_distance
-- name    : QEC.Coding.BDL26RandomPerturbation.common_hits_anchor_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:19.182492+00:00
-- url     : https://prove2.me/theorems/f4147d2f-3ec7-45f8-9937-f0f33752fcc9
-- title:
--   BDL26 Random Perturbation: common hits anchor distance
-- statement:
--   A common unit ball forces the unscaled anchors into the fixed local pool.
--   The extra two units absorb both unit-ball radii at every integral lambda >= 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L47-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L47-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.common_hits_anchor_distance (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t alpha lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 1 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ alpha*lambda) (a b : Triangle P) (z : Space)
    (ha : (oldTriangleImage P (perturbedMap P J lambda p) a ∩ Metric.closedBall z 1).Nonempty)
    (hb : (oldTriangleImage P (perturbedMap P J lambda p) b ∩ Metric.closedBall z 1).Nonempty) :
    dist (oldAnchor P J a) (oldAnchor P J b) ≤ 2*alpha+4 := by sorry
