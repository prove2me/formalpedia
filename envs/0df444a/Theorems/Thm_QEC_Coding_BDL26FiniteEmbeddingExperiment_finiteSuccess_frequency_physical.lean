-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_frequency_physical
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_frequency_physical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:45:12.156269+00:00
-- url     : https://prove2.me/theorems/f50860e7-95c7-47a5-89bd-35174e67d6c5
-- title:
--   BDL26 Finite Embedding Experiment: finite Success frequency physical
-- statement:
--   Every actual full-H real frequency uses the very same metric region on this event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L118-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean#L118-L131

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_frequency_physical {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1))
    (q : Physical (perturbationOddScale p) i.val) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.coupling (perturbationOddScale p) i.val q a) ω) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      ∀ s ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).selected.card ≤ 50 := by sorry
