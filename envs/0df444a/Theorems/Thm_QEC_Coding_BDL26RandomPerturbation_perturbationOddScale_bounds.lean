-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationOddScale_bounds
-- name    : QEC.Coding.BDL26RandomPerturbation.perturbationOddScale_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:12:59.769407+00:00
-- url     : https://prove2.me/theorems/ff859a6a-60a5-4275-97d6-145be70caaf3
-- title:
--   BDL26 Random Perturbation: perturbation Odd Scale bounds
-- statement:
--   The BDL26 Random Perturbation construction uses the perturbation Odd Scale bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L21-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L21-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.perturbationOddScale_bounds {L : ℝ} (p : GeometricParameters L) :
    (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ) < (perturbationOddScale p).ell ∧
      ((perturbationOddScale p).ell : ℝ) ≤ (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ)+2 := by sorry
