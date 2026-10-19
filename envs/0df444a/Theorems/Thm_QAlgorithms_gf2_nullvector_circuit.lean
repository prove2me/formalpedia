-- Prove2me | Theorems.Thm_QAlgorithms_gf2_nullvector_circuit
-- name    : QAlgorithms.gf2_nullvector_circuit
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T21:48:19.376243+00:00
-- url     : https://prove2.me/theorems/8ed9c45d-67a7-44d4-8708-13849a1a1718
-- title:
--   Cubic-size Boolean circuit for a nonzero nullvector of a full-row-rank binary matrix
-- statement:
--   There are constants $C>0$ and $N_0$ such that for every $n\ge N_0$ there is a Boolean circuit $G_n$ with $(n-1)n$ input bits, $n$ output bits, and at most $Cn^3$ AND, OR and NOT gates. For every matrix $A\in\mathbb F_2^{(n-1)\times n}$ with linearly independent rows, its row-major input produces a vector satisfying
--
--   $$
--   y=G_n(A)\ne0,\qquad Ay=0.
--   $$
--
--   The same circuit works for every full-row-rank input matrix of that size. This is the classical linear-system reconstruction step in Simon's algorithm, formulated independently of an oracle or hidden mask.
--
--   **Formalization Note.** Circuits use the existing straight-line model with two-input AND/OR gates and one-input NOT gates. The asymptotic threshold absorbs dimensions without input wires. Rows and outputs are bit strings; the shared conversion to $\mathbb F_2^n$ defines linear independence, and the shared parity dot product expresses the homogeneous equations.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, §3.2, PDF p.35 (printed p.24), paragraph after the final Simon state: Gaussian elimination modulo 2 with a classical circuit of size O(n^3). https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_DeWolf_Ch03_Model
set_option autoImplicit false
open QAlgorithms QAlgorithms.DeWolf

theorem QAlgorithms.gf2_nullvector_circuit :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ G : BoolCircuit ((n - 1) * n) n,
      G.WellFormed ∧ (G.size : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
      ∀ js : Fin (n - 1) → Qubits n,
        LinearIndependent (ZMod 2) (fun k => simonBitsToZMod2 (js k)) →
        let y := G.eval (fun p => js (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
        y ≠ 0 ∧ ∀ k, dotBits (js k) y = false := by sorry
