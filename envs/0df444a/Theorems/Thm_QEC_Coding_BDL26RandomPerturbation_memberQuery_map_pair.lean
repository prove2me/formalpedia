-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_memberQuery_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.memberQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:04:46.719761+00:00
-- url     : https://prove2.me/theorems/6c5dbdcc-dcfb-484d-b010-df49436e8dc3
-- title:
--   BDL26 Random Perturbation: member Query map pair
-- statement:
--   The BDL26 Random Perturbation construction uses the member Query map pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L173-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L173-L179

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

theorem QEC.Coding.BDL26RandomPerturbation.memberQuery_map_pair {A B : Type*} (encode : A → B)
    (eq : A → A → Bool × ℕ) (eq' : B → B → Bool × ℕ)
    (heq : ∀ a b, eq' (encode a) (encode b) = eq a b) (a : A) (L : List A) :
    memberQuery eq' (encode a) (L.map encode) = memberQuery eq a L := by sorry
