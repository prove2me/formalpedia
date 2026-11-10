-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_normalizedDisplacement_smul
-- name    : QEC.Coding.BDL26RandomPerturbation.normalizedDisplacement_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:43:18.988392+00:00
-- url     : https://prove2.me/theorems/1f928899-3233-417d-b4f5-142abd29ac63
-- title:
--   BDL26 Random Perturbation: normalized Displacement smul
-- statement:
--   The BDL26 Random Perturbation construction uses the normalized Displacement smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L16-L18
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SupportGeometry.lean#L16-L18

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.normalizedDisplacement_smul (p : Space) {R : ℝ} (hR : 0 < R) (hp : ‖p‖ = R) :
    R • (normalizedDisplacement p hR hp : Space) = p := by sorry
