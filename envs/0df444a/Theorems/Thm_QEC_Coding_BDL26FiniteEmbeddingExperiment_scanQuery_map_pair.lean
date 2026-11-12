-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_scanQuery_map_pair
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.scanQuery_map_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:50:25.060193+00:00
-- url     : https://prove2.me/theorems/9248d77a-b264-4e90-8dd7-78c4051583ba
-- title:
--   BDL26 Finite Embedding Experiment: scan Query map pair
-- statement:
--   Relabeling a counted scan preserves its branch-by-branch numeric cost.
--   Concrete uses must prove the query equality, including the cost component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L25-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L25-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.scanQuery_map_pair {A B W : Type*} (encode : A → B)
    (qA : A → W → Bool × ℕ) (qB : B → W → Bool × ℕ)
    (hquery : ∀ a w, qB (encode a) w = qA a w) (rows : List A) (w : W) :
    scanQuery qB (rows.map encode) w =
      ((scanQuery qA rows w).1.map encode, (scanQuery qA rows w).2) := by sorry
