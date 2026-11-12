-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_mem_ballSubsystem
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.mem_ballSubsystem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:46:01.471369+00:00
-- url     : https://prove2.me/theorems/cea3a694-1152-4429-8fce-83f6e8f67389
-- title:
--   BDL26 Native Hamiltonian Locality: mem ball Subsystem
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the mem ball Subsystem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L30-L34

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.mem_ballSubsystem (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ) (q : Physical S n) :
    q ∈ (ballSubsystem S n J c r).selected ↔ dist (J (.q q)) c ≤ r := by sorry
