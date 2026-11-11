-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:20:54.499004+00:00
-- url     : https://prove2.me/theorems/10706d5a-419f-466a-90c2-53a12027d53c
-- title:
--   BDL26 Finite Embedding Experiment: finite Success geometry
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the finite Success geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L112-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L112-L115

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_geometry {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1)) :
    PhysicalGeometry (perturbationOddScale p) i.val (history p n z i) p.t := by sorry
