-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_cost_congr
-- name    : QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:11:39.552215+00:00
-- url     : https://prove2.me/theorems/fb573f2e-e9e3-45ea-b562-2b9451e0d6ac
-- title:
--   BDL26 Random Perturbation: map Query cost congr
-- statement:
--   The BDL26 Random Perturbation construction uses the map Query cost congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L565-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L565-L570

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

theorem QEC.Coding.BDL26RandomPerturbation.mapQuery_cost_congr {A B C : Type*} (q : A → B × ℕ) (q' : A → C × ℕ)
    (hq : ∀ a, (q a).2 = (q' a).2) (L : List A) :
    (mapQuery q L).2 = (mapQuery q' L).2 := by sorry
