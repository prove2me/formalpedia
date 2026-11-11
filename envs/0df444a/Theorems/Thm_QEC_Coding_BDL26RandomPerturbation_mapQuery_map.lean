-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_map
-- name    : QEC.Coding.BDL26RandomPerturbation.mapQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:04.135929+00:00
-- url     : https://prove2.me/theorems/74c7dc61-1cc2-4650-b0cc-66a415b58be7
-- title:
--   BDL26 Random Perturbation: map Query map
-- statement:
--   The BDL26 Random Perturbation construction uses the map Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L559-L563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L559-L563

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

theorem QEC.Coding.BDL26RandomPerturbation.mapQuery_map {A B C : Type*} (q : B → C × ℕ) (f : A → B) (L : List A) :
    mapQuery q (L.map f) = mapQuery (fun a => q (f a)) L := by sorry
