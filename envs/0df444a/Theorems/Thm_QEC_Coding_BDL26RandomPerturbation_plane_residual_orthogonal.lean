-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_plane_residual_orthogonal
-- name    : QEC.Coding.BDL26RandomPerturbation.plane_residual_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:44:07.19705+00:00
-- url     : https://prove2.me/theorems/3de62b19-ce91-4dec-a333-786e471473a8
-- title:
--   BDL26 Random Perturbation: plane residual orthogonal
-- statement:
--   The BDL26 Random Perturbation construction uses the plane residual orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L50-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L50-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.plane_residual_orthogonal (b c d : Space) (hdet : gramDet b c ≠ 0) :
    inner ℝ (d-(planeU b c d • b+planeV b c d • c)) b = 0 ∧
      inner ℝ (d-(planeU b c d • b+planeV b c d • c)) c = 0 := by sorry
