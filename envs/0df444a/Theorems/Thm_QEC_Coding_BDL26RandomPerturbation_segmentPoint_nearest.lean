-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segmentPoint_nearest
-- name    : QEC.Coding.BDL26RandomPerturbation.segmentPoint_nearest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:16.064085+00:00
-- url     : https://prove2.me/theorems/03b505c5-b0e6-4884-8f5b-42c6cf68870d
-- title:
--   BDL26 Random Perturbation: segment Point nearest
-- statement:
--   No division assumption is needed when the endpoints coincide.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L55-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L55-L68

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.segmentPoint_nearest (a b z : Space) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist z (segmentPoint a b z) ≤ dist z (a+t • (b-a)) := by sorry
