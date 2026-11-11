-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_cost_constant
-- name    : QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:10:47.347193+00:00
-- url     : https://prove2.me/theorems/e002b404-ac11-4a6a-ab2f-c34d759e418c
-- title:
--   BDL26 Random Perturbation: map Query cost constant
-- statement:
--   The BDL26 Random Perturbation construction uses the map Query cost constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L572-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L572-L579

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

theorem QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_constant {A B : Type*} (q : A → B × ℕ) (c : ℕ)
    (hq : ∀ a, (q a).2 = c) (L : List A) :
    (mapQuery q L).2 = L.length * (c + 1) := by sorry
