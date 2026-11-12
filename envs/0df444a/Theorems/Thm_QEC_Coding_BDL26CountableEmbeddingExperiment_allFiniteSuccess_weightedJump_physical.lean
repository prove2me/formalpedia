-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_weightedJump_physical
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_weightedJump_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:41:55.758206+00:00
-- url     : https://prove2.me/theorems/7fc55275-012d-4c31-afaf-b10d247dfadb
-- title:
--   BDL26 Countable Embedding Experiment: all Finite Success weighted Jump physical
-- statement:
--   The BDL26 Countable Embedding Experiment construction uses the all Finite Success weighted Jump physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L108-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean#L108-L126

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_weightedJump_physical {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n → ℝ)
    (q : Physical (perturbationOddScale p) n) (a : CSSDaviesLocality.Axis)
    (w : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) n)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n =>
          BDL26CSSDaviesLocality.coupling (perturbationOddScale p) n qa.1 qa.2)
        rate ((q,a),w)) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      ∀ s ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).selected.card ≤ 50 := by sorry
