-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segment_distance_sq
-- name    : QEC.Coding.BDL26RandomPerturbation.segment_distance_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:18.102464+00:00
-- url     : https://prove2.me/theorems/faeb9a19-4c86-4fe3-8fb7-9e3aab63c3e1
-- title:
--   BDL26 Random Perturbation: segment distance sq
-- statement:
--   The BDL26 Random Perturbation construction uses the segment distance sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L47-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean#L47-L52

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.segment_distance_sq (a b z : Space) (t : ℝ) :
    ‖z-(a+t • (b-a))‖^2 =
      ‖z-a‖^2-2*t*inner ℝ (z-a) (b-a)+t^2*‖b-a‖^2 := by sorry
