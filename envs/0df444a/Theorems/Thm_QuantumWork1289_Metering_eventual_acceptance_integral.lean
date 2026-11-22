-- Prove2me | Theorems.Thm_QuantumWork1289_Metering_eventual_acceptance_integral
-- name    : QuantumWork1289.Metering.eventual_acceptance_integral
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T16:44:44.574948+00:00
-- url     : https://prove2.me/theorems/b696b3ca-c991-4319-afeb-32c4faef5713
-- title:
--   Eventual acceptance as the integral of pointwise horizon limits
-- statement:
--   For each fixed seed and oracle, the accepted Born mass of a hybrid machine increases monotonically with execution time. If its finite executions are measurable, the success probability equals the integral of their pointwise supremum even when the machine may run forever.
-- source:
--   Operational supporting lemma for STOC 2027 #1289, Mohammed Barhoush, Proof of Quantum Work with Classical Verification, formal Theorem 4 (p. 18), in the published finite-horizon oracle experiment model.

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment

set_option autoImplicit false
open QuantumWork1289.Metering MeasureTheory
open scoped ENNReal

theorem QuantumWork1289.Metering.eventual_acceptance_integral {X B O Ω S : Type} [Fintype B] [Nonempty B] [DecidableEq B]
    [AddCommGroup B] [MeasurableSpace B] [MeasurableSpace Ω]
    {n : ℕ} (A : SeededMachine X B O Ω S n) (μ : Measure Ω)
    (accept : (X → B) → O → Prop) (h : MeasurableExecution A μ accept) :
    (∀ ω f, Monotone (fun t => acceptedMass (A.machine ω) (A.initialState ω) accept t f)) ∧
      successProbability A μ accept = ∫⁻ p : Ω × (X → B),
        ⨆ t : ℕ, acceptedMass (A.machine p.1) (A.initialState p.1) accept t p.2
        ∂(μ.prod (oracleLaw X B)) := by sorry
