-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stream_freshPair_law
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.stream_freshPair_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:10:34.199719+00:00
-- url     : https://prove2.me/theorems/78ce459a-4671-44d9-ae26-ccb8f79d6907
-- title:
--   BDL26 Countable Embedding Experiment: stream fresh Pair law
-- statement:
--   An independent fresh table paired with the recursively dependent input map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L147-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean#L147-L160

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.stream_freshPair_law {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => (levelMap p omega n, omega n)) =
      (outputLaw p n).prod (physicalTableLaw p n) := by sorry
