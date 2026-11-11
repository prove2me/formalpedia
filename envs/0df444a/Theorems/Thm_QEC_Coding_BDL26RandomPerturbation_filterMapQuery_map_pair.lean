-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.filterMapQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:26:09.373243+00:00
-- url     : https://prove2.me/theorems/745ed6b0-da39-4183-b9fb-476a9f35dceb
-- title:
--   BDL26 Random Perturbation: filter Map Query map pair
-- statement:
--   Relabeling keeps the original filtering decisions and every charged operation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L163-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L163-L171

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

theorem QEC.Coding.BDL26RandomPerturbation.filterMapQuery_map_pair {A B C : Type*} (encode : B → C)
    (q : A → Option B × ℕ) (q' : A → Option C × ℕ)
    (hq : ∀ a, q' a = ((q a).1.map encode, (q a).2)) (L : List A) :
    filterMapQuery q' L = ((filterMapQuery q L).1.map encode, (filterMapQuery q L).2) := by sorry
