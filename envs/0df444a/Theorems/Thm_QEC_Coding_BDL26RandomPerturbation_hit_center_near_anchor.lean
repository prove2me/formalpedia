-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_hit_center_near_anchor
-- name    : QEC.Coding.BDL26RandomPerturbation.hit_center_near_anchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:13:06.11236+00:00
-- url     : https://prove2.me/theorems/d2043e9d-fd75-47f2-be50-742b7381928f
-- title:
--   BDL26 Random Perturbation: hit center near anchor
-- statement:
--   The BDL26 Random Perturbation construction uses the hit center near anchor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L32-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/HitGeometry.lean#L32-L43

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_HitGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.hit_center_near_anchor (P : TannerSquarePresentation)
    (J p : Vertex P → Space) (t R lambda : ℝ)
    (hJ : IsBoundedDensityLocalMap P J t) (hl : 0 ≤ lambda)
    (hp : ∀ v, ‖p v‖ ≤ R) (a : Triangle P) (z : Space)
    (hit : (oldTriangleImage P (perturbedMap P J lambda p) a ∩
      Metric.closedBall z 1).Nonempty) :
    dist z (lambda • oldAnchor P J a) ≤ R+lambda+1 := by sorry
