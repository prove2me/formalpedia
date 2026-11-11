-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedScan_map_pair
-- name    : QEC.Coding.BDL26RandomPerturbation.countedScan_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:14:58.830477+00:00
-- url     : https://prove2.me/theorems/23f2d1c5-b39c-43f5-a7eb-216673ce5d01
-- title:
--   BDL26 Random Perturbation: counted Scan map pair
-- statement:
--   The BDL26 Random Perturbation construction uses the counted Scan map pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L508-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L508-L516

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

theorem QEC.Coding.BDL26RandomPerturbation.countedScan_map_pair {A B W : Type*} (encode : A → B)
    (q : A → W → Bool × ℕ) (q' : B → W → Bool × ℕ)
    (hq : ∀ a w, q' (encode a) w = q a w) (L : List A) (w : W) :
    scanQuery q' (L.map encode) w = ((scanQuery q L w).1.map encode, (scanQuery q L w).2) := by sorry
