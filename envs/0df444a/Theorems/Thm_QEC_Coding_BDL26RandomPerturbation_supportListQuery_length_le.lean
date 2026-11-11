-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supportListQuery_length_le
-- name    : QEC.Coding.BDL26RandomPerturbation.supportListQuery_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:53:19.294521+00:00
-- url     : https://prove2.me/theorems/7e73e0c0-5b51-4332-83c2-f1a35b76875e
-- title:
--   BDL26 Random Perturbation: support List Query length le
-- statement:
--   The BDL26 Random Perturbation construction uses the support List Query length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L92-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L92-L102

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.supportListQuery_length_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) : (supportListQuery P J r e).1.length ≤ 12 := by sorry
