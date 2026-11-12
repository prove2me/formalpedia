-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_source_even_hamiltonian
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.source_even_hamiltonian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:45:47.341907+00:00
-- url     : https://prove2.me/theorems/ae86b769-3f8c-4e77-ba12-a7056af3202d
-- title:
--   BDL26 Native Hamiltonian Locality: source even hamiltonian
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the source even hamiltonian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L198-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L198-L203

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26NativeHamiltonianLocality.source_even_hamiltonian {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (2*k),
      HamiltonianGeometry (perturbationOddScale p) (2*k)
        (BDL26NativeFiniteComposition.evaluate p (2*k) z) p.t := by sorry
