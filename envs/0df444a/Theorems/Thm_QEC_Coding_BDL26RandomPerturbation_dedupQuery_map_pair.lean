-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dedupQuery_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.dedupQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:05:38.947196+00:00
-- url     : https://prove2.me/theorems/4c7e0b01-4489-4328-87e5-4785e77d839f
-- title:
--   BDL26 Random Perturbation: dedup Query map pair
-- statement:
--   The BDL26 Random Perturbation construction uses the dedup Query map pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L181-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L181-L190

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

theorem QEC.Coding.BDL26RandomPerturbation.dedupQuery_map_pair {A B : Type*} (encode : A → B)
    (eq : A → A → Bool × ℕ) (eq' : B → B → Bool × ℕ)
    (heq : ∀ a b, eq' (encode a) (encode b) = eq a b) (L : List A) :
    dedupQuery eq' (L.map encode) =
      ((dedupQuery eq L).1.map encode, (dedupQuery eq L).2) := by sorry
