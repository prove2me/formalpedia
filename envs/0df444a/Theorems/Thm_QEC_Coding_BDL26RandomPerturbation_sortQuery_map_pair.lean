-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.sortQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:26:12.844942+00:00
-- url     : https://prove2.me/theorems/66219c72-f7d2-445e-9f2b-198cf9437190
-- title:
--   BDL26 Random Perturbation: sort Query map pair
-- statement:
--   The BDL26 Random Perturbation construction uses the sort Query map pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L203-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L203-L210

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

theorem QEC.Coding.BDL26RandomPerturbation.sortQuery_map_pair {A B : Type*} (encode : A → B)
    (cmp : A → A → Bool × ℕ) (cmp' : B → B → Bool × ℕ)
    (hc : ∀ a b, cmp' (encode a) (encode b) = cmp a b) (L : List A) :
    sortQuery cmp' (L.map encode) = ((sortQuery cmp L).1.map encode, (sortQuery cmp L).2) := by sorry
