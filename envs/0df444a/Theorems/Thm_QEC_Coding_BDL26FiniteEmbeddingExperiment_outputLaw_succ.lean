-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_succ
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:16:25.509527+00:00
-- url     : https://prove2.me/theorems/0fe1c843-eecc-41f3-8b3b-28d7094f0929
-- title:
--   BDL26 Finite Embedding Experiment: output Law succ
-- statement:
--   The incoming law is first in `bind`; the same total successor kernel is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L206-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean#L206-L210

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    outputLaw p (n+1) = (successorKernel p n) ∘ₘ (outputLaw p n) := by sorry
