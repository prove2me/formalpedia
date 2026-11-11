-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_stateTrianglePointsQuery_map
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_stateTrianglePointsQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:12:29.56198+00:00
-- url     : https://prove2.me/theorems/62fa3a1d-f506-45d7-997b-89d42ca6adc6
-- title:
--   BDL26 Random Perturbation: measurable state Triangle Points Query map
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable state Triangle Points Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L400-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L400-L424

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_stateTrianglePointsQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (t : Triangle P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))) := by sorry
