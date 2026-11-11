-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_coordinateAxis_orthogonal
-- name    : QEC.Coding.BDL26RandomPerturbation.coordinateAxis_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:47:28.277236+00:00
-- url     : https://prove2.me/theorems/0d70da94-468b-411a-9399-2450e1759456
-- title:
--   BDL26 Random Perturbation: coordinate Axis orthogonal
-- statement:
--   The BDL26 Random Perturbation construction uses the coordinate Axis orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L19-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Geometry.lean#L19-L21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.coordinateAxis_orthogonal {i j : Fin 3} (h : i ≠ j) :
    ⟪(coordinateAxis i : Space), (coordinateAxis j : Space)⟫_ℝ = 0 := by sorry
