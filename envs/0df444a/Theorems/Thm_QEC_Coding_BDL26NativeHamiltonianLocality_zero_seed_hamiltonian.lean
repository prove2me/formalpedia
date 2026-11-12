-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_zero_seed_hamiltonian
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.zero_seed_hamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:45:28.67592+00:00
-- url     : https://prove2.me/theorems/8d073aa8-0d23-4778-9819-9d2bf9c11a20
-- title:
--   BDL26 Native Hamiltonian Locality: zero seed hamiltonian
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the zero seed hamiltonian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L169-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L169-L174

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.zero_seed_hamiltonian {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    HamiltonianGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t := by sorry
