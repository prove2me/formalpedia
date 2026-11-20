-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_fixed_parameters_all_finite
-- name    : QEC.Coding.BDL26NativeDaviesLocality.fixed_parameters_all_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:08:32.840688+00:00
-- url     : https://prove2.me/theorems/5f8abf6f-e3db-40e0-ae06-b78a2a99fd73
-- title:
--   BDL26 Native Davies Locality: fixed parameters all finite
-- statement:
--   One legal parameter is chosen before all finite depths. The ORIGINAL total
--   coordinate cost is retained. This asserts no paid computation of spectral
--   matrices, local restrictions or subsystem certificates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L203-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeDaviesLocality.lean#L203-L226

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_fixed_parameters_all_finite
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_fixed_parameters_all_finite

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26NativeDaviesLocality.fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) ≤
        (BDL26NativeFiniteComposition.totalCoefficient p*
          (BDL26FiniteEmbeddingExperiment.stageQubits p N+1)^1774 : ℕ) ∧
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) < ∞ ∧
      Integrable (fun z => (BDL26NativeFiniteComposition.totalCost p N z).toReal)
        (BDL26NativeFiniteComposition.experimentLaw p N) ∧
      BDL26NativeFiniteComposition.experimentLaw p N (finiteDaviesSuccess p N) = 1 ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N,
        z ∈ finiteDaviesSuccess p N ∧
        BDL26NativeFiniteComposition.totalCost p N z < ∞ ∧
        ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
          (BDL26NativeFiniteComposition.history p N z i) p.t := by sorry
