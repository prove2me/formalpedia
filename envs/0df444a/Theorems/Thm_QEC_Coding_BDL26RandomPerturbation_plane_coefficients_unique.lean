-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_plane_coefficients_unique
-- name    : QEC.Coding.BDL26RandomPerturbation.plane_coefficients_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:30.449515+00:00
-- url     : https://prove2.me/theorems/b6e9ef5d-b7d6-4e81-b5e4-05beab392fb6
-- title:
--   BDL26 Random Perturbation: plane coefficients unique
-- statement:
--   The BDL26 Random Perturbation construction uses the plane coefficients unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L58-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L58-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.plane_coefficients_unique (b c d : Space) (hdet : gramDet b c ≠ 0)
    {u v : ℝ} (hb : ‖b‖^2*u+inner ℝ b c*v = inner ℝ d b)
    (hc : inner ℝ b c*u+‖c‖^2*v = inner ℝ d c) :
    u = planeU b c d ∧ v = planeV b c d := by sorry
