-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gram_residual_sq
-- name    : QEC.Coding.BDL26RandomPerturbation.gram_residual_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:21.090295+00:00
-- url     : https://prove2.me/theorems/95a5a4b7-c533-457d-9995-7bff55698f53
-- title:
--   BDL26 Random Perturbation: gram residual sq
-- statement:
--   The BDL26 Random Perturbation construction uses the gram residual sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L17-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GramProjection.lean#L17-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.gram_residual_sq (b c : Space) (hb : b ≠ 0) :
    ‖b‖^2*‖c-(inner ℝ b c/‖b‖^2) • b‖^2 = gramDet b c := by sorry
