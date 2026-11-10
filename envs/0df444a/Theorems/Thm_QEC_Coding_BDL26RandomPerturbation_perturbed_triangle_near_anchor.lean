-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbed_triangle_near_anchor
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbed_triangle_near_anchor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:06:40.510236+00:00
-- url     : https://prove2.me/theorems/03e384a5-554f-434f-bf0b-e219a0bde98f
-- title:
--   BDL26 Random Perturbation: perturbed triangle near anchor
-- statement:
--   Convexity keeps the entire perturbed triangle near its scaled old X anchor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L10-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L10-L30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.perturbed_triangle_near_anchor (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t R lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 0 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ R) (a : Triangle P) :
    oldTriangleImage P (perturbedMap P J lambda p) a ⊆
      Metric.closedBall (lambda • oldAnchor P J a) (R+lambda) := by sorry
