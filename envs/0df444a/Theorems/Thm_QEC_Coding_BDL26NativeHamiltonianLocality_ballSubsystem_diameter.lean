-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_ballSubsystem_diameter
-- name    : QEC.Coding.BDL26NativeHamiltonianLocality.ballSubsystem_diameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:25:31.66443+00:00
-- url     : https://prove2.me/theorems/5af13560-b097-44e5-98ed-40f482ef7f3b
-- title:
--   BDL26 Native Hamiltonian Locality: ball Subsystem diameter
-- statement:
--   The BDL26 Native Hamiltonian Locality construction uses the ball Subsystem diameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L36-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeHamiltonianLocality.lean#L36-L47

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

theorem QEC.Coding.BDL26NativeHamiltonianLocality.ballSubsystem_diameter (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ)
    (q u : Physical S n)
    (hq : q ∈ (ballSubsystem S n J c r).selected)
    (hu : u ∈ (ballSubsystem S n J c r).selected) :
    dist (J (.q q)) (J (.q u)) ≤ 2*r := by sorry
