-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_one_query_phase_preparation
-- name    : QuantumLTF.Membership.Supplement.one_query_phase_preparation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:22:34.520598+00:00
-- url     : https://prove2.me/theorems/8318873b-0ae8-42d3-838b-fdbd6e2d2f00
-- title:
--   One-query phase preparation with normalized branches
-- statement:
--   For every dimension $n$ and grid width $q$, there is a fixed circuit making one forward, uncontrolled quantum-example query and using one additional elementary gate. It has normalized branches $F_0$ and $F_w$, where $F_0$ is independent of the unknown direction, and its output amplitudes satisfy
--
--   $$\langle x,b|c^U|0\rangle=\frac{1}{\sqrt 2}\begin{cases}F_0(x),&b=0,\\F_w(x),&b=1.\end{cases}$$
--
--   The identity holds for every valid unitary extension $U$ of the quantum-example oracle. This is the phase-preparation step in Eq. (157), before the Hermite transform required for Theorem 5.2.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.1, Eq. (157), phase preparation in the proof of Theorem 5.2.

import Mathlib
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly
import Definitions.Def_QuantumLTF_Example_qex
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example QuantumLTF.Membership.Supplement

theorem QuantumLTF.Membership.Supplement.one_query_phase_preparation (n q : ℕ) :
    ∃ (c : OracleCircuit gates12 (fun _ : Fin 1 => n*q+1) (n*q+1))
      (F0 : EuclideanSpace ℂ (Qubits (n*q))),
      ‖F0‖ = 1 ∧ Uncontrolled c ∧ ForwardOnly c ∧ c.queryCount 0 = 1 ∧ c.gateCount = 1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n),
      ∀ U : Matrix (Qubits (n*q+1)) (Qubits (n*q+1)) ℂ, IsQEX (q := q) w U →
        ∃ Fw : EuclideanSpace ℂ (Qubits (n*q)), ‖Fw‖ = 1 ∧
          ∀ (x : Qubits (n*q)) (b : Bool),
            act (c.unitary (fun _ => U)) (zeroKet (n*q+1)) (Fin.snoc x b) =
              (1/Real.sqrt 2:ℂ)*(if b then Fw x else F0 x) := by sorry
