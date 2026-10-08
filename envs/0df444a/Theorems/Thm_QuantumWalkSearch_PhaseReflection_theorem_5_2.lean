-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_theorem_5_2
-- name    : QuantumWalkSearch.PhaseReflection.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:56.568996+00:00
-- url     : https://prove2.me/theorems/d34f3815-37f6-4f49-b57c-e21f40de29a1
-- title:
--   Theorem 5, property 2 — phase estimation fixes $|\psi\rangle|0^s\rangle$ when $U|\psi\rangle=|\psi\rangle$
-- statement:
--   Let $U$ be a unitary matrix on $\mathbb C^\iota$ ($\iota$ finite), $s\ge1$ an integer, and $C(U)$ the phase-estimation circuit with $s$ ancilla qubits. For every eigenvector $|\psi\rangle$ of $U$ with eigenvalue $1$, i.e. $U|\psi\rangle=|\psi\rangle$,
--   $$C(U)\,|\psi\rangle|0^s\rangle=|\psi\rangle|0^s\rangle .$$
--
--   This is the property of phase estimation that makes $R(P)$ fix $|\pi\rangle|0^{ks}\rangle$ exactly in Theorem 6.
--
--   **Formalization Note** The paper states Theorem 5 for $U$ of dimension $2^m\times2^m$, $m\ge1$; the statement here holds for any finite-dimensional $U$, which includes that case. Property 1 (gate counts) and the uniformity of the circuit family are not formalized.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 9, Theorem 5 (Cleve, Ekert, Macchiavello, Mosca [14]), property 2

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_PhaseEstimation

namespace QuantumWalkSearch.PhaseReflection

/-- Theorem 5, property 2 (p. 9): phase estimation fixes `|ψ⟩|0^s⟩` when `U|ψ⟩ = |ψ⟩`. -/
theorem theorem_5_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (s : ℕ) (hs : 1 ≤ s) (ψ : EuclideanSpace ℂ ι)
    (hψ : Matrix.toEuclideanLin U ψ = ψ) :
    Matrix.toEuclideanLin (phaseEstimation U s) (tensorZero ψ) =
      (tensorZero ψ : EuclideanSpace ℂ (ι × Fin (2 ^ s))) := by sorry

end QuantumWalkSearch.PhaseReflection
