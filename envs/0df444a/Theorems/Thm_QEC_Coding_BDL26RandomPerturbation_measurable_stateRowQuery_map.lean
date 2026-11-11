-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_stateRowQuery_map
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_stateRowQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:30.783492+00:00
-- url     : https://prove2.me/theorems/d86bef7c-fb6f-4ccc-a9fd-3a1240da13c6
-- title:
--   BDL26 Random Perturbation: measurable state Row Query map
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable state Row Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L370-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L370-L383

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
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26RandomPerturbation.measurable_stateRowQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (v : Vertex P) (L : List (Vertex P))
    (f : Vertex P → Ω → ℕ × Space) (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => stateRowQuery v (L.map (fun u => (u, f u w)))) := by sorry
