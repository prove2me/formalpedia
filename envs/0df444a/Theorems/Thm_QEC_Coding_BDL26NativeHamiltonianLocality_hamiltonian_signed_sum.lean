-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_hamiltonian_signed_sum
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.hamiltonian_signed_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:27:08.92518+00:00
-- url     : https://prove2.me/theorems/fcd70509-3f2a-4b21-95f4-1eb3ea59fc2e
-- title:
--   BDL26 Native Hamiltonian Locality: hamiltonian signed sum
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the hamiltonian signed sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L54-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L54-L56

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.hamiltonian_signed_sum (S : OddScale) (n : ℕ) :
    hamiltonian S n = ∑ j : Sum (ZLabel S n) (XLabel S n), signedCheck S n j := by sorry
