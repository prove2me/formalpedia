-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_theorem_5_3
-- name    : QuantumWalkSearch.PhaseReflection.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:29.484606+00:00
-- url     : https://prove2.me/theorems/bb33f4e1-2fb7-4753-a6ee-7945fc7d6ae7
-- title:
--   Theorem 5, property 3 — on an $e^{2i\theta}$-eigenvector, $C(U)|\psi\rangle|0^s\rangle=|\psi\rangle|\omega\rangle$ with $|\langle0^s|\omega\rangle|=|\sin(2^s\theta)|/(2^s\sin\theta)$
-- statement:
--   Let $U$ be a unitary matrix on $\mathbb C^\iota$ ($\iota$ finite), $s\ge1$ an integer, and $C(U)$ the phase-estimation circuit with $s$ ancilla qubits. If $|\psi\rangle\neq0$ and $U|\psi\rangle=e^{2i\theta}|\psi\rangle$ with $\theta\in(0,\pi)$, then there is an $s$-qubit state $|\omega\rangle$ (a unit vector of $\mathbb C^{2^s}$) such that
--   $$C(U)\,|\psi\rangle|0^s\rangle=|\psi\rangle|\omega\rangle\qquad\text{and}\qquad |\langle0^s|\omega\rangle|=\frac{|\sin(2^s\theta)|}{2^s\sin\theta}.$$
--
--   In words, phase estimation leaves the eigenvector in the system register and writes into the ancilla a state whose amplitude on the "phase $0$" outcome is the Fejér-type ratio above; the proof of Theorem 6 bounds this ratio by $1/2$ away from $\theta=0$.
--
--   **Formalization Note** The paper prints $|\langle0^s|\omega\rangle|=\sin(2^s\theta)/(2^s\sin\theta)$; the right side can be negative for $\theta\in(0,\pi)$ (e.g. $s=1$, $\theta\in(\pi/2,\pi)$), so the modulus $|\sin(2^s\theta)|$ is used. Stated for any finite-dimensional $U$ (the paper: $2^m\times2^m$). Property 1 (gate counts) and uniformity are not formalized.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 9, Theorem 5 (Cleve, Ekert, Macchiavello, Mosca [14]), property 3

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_PhaseEstimation

namespace QuantumWalkSearch.PhaseReflection

/-- Theorem 5, property 3 (p. 9), with the modulus on `sin(2^s θ)`: if `U|ψ⟩ = e^{2iθ}|ψ⟩`, `ψ ≠ 0`,
`θ ∈ (0, π)`, then `C(U)|ψ⟩|0^s⟩ = |ψ⟩|ω⟩` for a unit vector `ω ∈ ℂ^{2^s}` with
`|⟨0^s|ω⟩| = |sin(2^s θ)| / (2^s sin θ)`. -/
theorem theorem_5_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (s : ℕ) (hs : 1 ≤ s) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (ψ : EuclideanSpace ℂ ι) (hψ0 : ψ ≠ 0)
    (hψ : Matrix.toEuclideanLin U ψ = Complex.exp (2 * (θ : ℂ) * Complex.I) • ψ) :
    ∃ ω : EuclideanSpace ℂ (Fin (2 ^ s)), ‖ω‖ = 1 ∧
      Matrix.toEuclideanLin (phaseEstimation U s) (tensorZero ψ) = tensorVec ψ ω ∧
      ‖ω 0‖ = |Real.sin (2 ^ s * θ)| / (2 ^ s * Real.sin θ) := by sorry

end QuantumWalkSearch.PhaseReflection
