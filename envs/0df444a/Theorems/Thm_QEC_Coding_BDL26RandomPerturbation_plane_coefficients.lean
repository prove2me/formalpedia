-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_plane_coefficients
-- name    : QEC.Coding.BDL26RandomPerturbation.plane_coefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:36.486978+00:00
-- url     : https://prove2.me/theorems/d56f64e5-b79b-4811-9edb-8a629296ee4d
-- title:
--   BDL26 Random Perturbation: plane coefficients
-- statement:
--   The BDL26 Random Perturbation construction uses the plane coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L41-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L41-L48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.plane_coefficients (b c d : Space) (hdet : gramDet b c ≠ 0) :
    ‖b‖^2*planeU b c d+inner ℝ b c*planeV b c d = inner ℝ d b ∧
      inner ℝ b c*planeU b c d+‖c‖^2*planeV b c d = inner ℝ d c := by sorry
