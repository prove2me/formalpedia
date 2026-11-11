-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_orderedInsertQuery_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:06:19.473964+00:00
-- url     : https://prove2.me/theorems/da2bea39-5b78-4549-b8ef-f757d342bde9
-- title:
--   BDL26 Random Perturbation: ordered Insert Query map pair
-- statement:
--   The BDL26 Random Perturbation construction uses the ordered Insert Query map pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L192-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L192-L201

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

theorem QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_map_pair {A B : Type*} (encode : A → B)
    (cmp : A → A → Bool × ℕ) (cmp' : B → B → Bool × ℕ)
    (hc : ∀ a b, cmp' (encode a) (encode b) = cmp a b) (a : A) (L : List A) :
    orderedInsertQuery cmp' (encode a) (L.map encode) =
      ((orderedInsertQuery cmp a L).1.map encode, (orderedInsertQuery cmp a L).2) := by sorry
