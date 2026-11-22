-- Prove2me | Theorems.Thm_QuantumWork1289_Metering_finite_horizon_mass
-- name    : QuantumWork1289.Metering.finite_horizon_mass
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T16:21:53.233525+00:00
-- url     : https://prove2.me/theorems/e0e06b29-24fd-44c5-b42f-d48f218479a2
-- title:
--   Finite-horizon probability conservation for the hybrid query experiment
-- statement:
--   In the published hybrid-query execution model, start from a positive density matrix of trace one and run any finite horizon. The sum of the Born masses of all terminal and frontier branches is exactly one. The mass of accepted branches for any predicate is therefore at most one. This establishes the normalization of the finite-horizon experiment used in Theorem 4.
-- source:
--   Supporting lemma for Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289, Theorem 4 (p. 18). The statement uses the published Lean hybridMachine definition and its finite-horizon execute and acceptedMass directly.

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_hybridMachine

set_option autoImplicit false
open QuantumWork1289.Metering
open scoped ENNReal

theorem QuantumWork1289.Metering.finite_horizon_mass {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (ρ : InitialState n)
    (accept : (X → B) → O → Prop) (t : ℕ) (f : X → B) :
    ((execute A f t A.initial ρ.matrix).map branchMass).sum = 1 ∧
      acceptedMass A ρ accept t f ≤ 1 := by sorry
