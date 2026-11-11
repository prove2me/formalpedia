-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_good_ae
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.history_good_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:24:03.331047+00:00
-- url     : https://prove2.me/theorems/2e9ec09b-5044-4686-bfa9-de4de96ca319
-- title:
--   BDL26 Finite Embedding Experiment: history good ae
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the history good ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L41-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L41-L47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.history_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin (n+1)) :
    ∀ᵐ z ∂experimentLaw p n,
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t := by sorry
