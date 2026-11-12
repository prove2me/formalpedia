-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_finite_history_hamiltonian_ae
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.finite_history_hamiltonian_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:06:36.438449+00:00
-- url     : https://prove2.me/theorems/d5e537e4-09ec-4a5b-a209-9b4afcaa0ba5
-- title:
--   BDL26 Native Hamiltonian Locality: finite history hamiltonian ae
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the finite history hamiltonian ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L137-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L137-L142

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.finite_history_hamiltonian_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N, ∀ i : Fin (N+1),
      HamiltonianGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by sorry
