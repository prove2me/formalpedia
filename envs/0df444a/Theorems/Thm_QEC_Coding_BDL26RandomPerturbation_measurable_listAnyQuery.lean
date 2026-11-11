-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAnyQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_listAnyQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:08:55.740221+00:00
-- url     : https://prove2.me/theorems/b2e26940-230c-4a05-83ee-2fe5ad488393
-- title:
--   BDL26 Random Perturbation: measurable list Any Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable list Any Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L104-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L104-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.measurable_listAnyQuery {Ω A : Type*} [MeasurableSpace Ω]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => listAnyQuery (fun a => q a w) L) := by sorry
