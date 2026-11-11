-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lll_resampling_budget_le_one
-- name    : QEC.Coding.BDL26RandomPerturbation.lll_resampling_budget_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:45:08.889939+00:00
-- url     : https://prove2.me/theorems/5faf1540-b547-4296-ab35-88cb47153321
-- title:
--   BDL26 Random Perturbation: lll resampling budget le one
-- statement:
--   The BDL26 Random Perturbation construction uses the lll resampling budget le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedSteps.lean#L18-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedSteps.lean#L18-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.lll_resampling_budget_le_one {I : Type*} (D : ℕ) (i : I) :
    resamplingBudget (fun _ : I => lllWeight D) i ≤ 1 := by sorry
