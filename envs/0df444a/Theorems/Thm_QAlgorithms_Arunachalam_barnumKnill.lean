-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_barnumKnill
-- name    : QAlgorithms.Arunachalam.barnumKnill
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:16.980091+00:00
-- url     : https://prove2.me/theorems/2a1d1bf4-9e1f-49d0-9115-4026c1749193
-- title:
--   Barnum–Knill: the pretty good measurement is at most quadratically worse than optimal
-- statement:
--   Let $E=\{(p_i,|\psi_i\rangle)\}_{i\in[m]}$ be an ensemble of pure states $|\psi_i\rangle\in\mathbb C^d$ (unit vectors) with probabilities $p_i\ge 0$, $\sum_i p_i=1$. For an $m$-outcome POVM $M=\{M_i\}$ (positive semidefinite matrices summing to the identity), the average success probability is $P_M(E)=\sum_i p_i\langle\psi_i|M_i|\psi_i\rangle$, and $P^{\mathrm{opt}}(E)=\max_M P_M(E)$.
--
--   The pretty good measurement is built from $|\psi_i'\rangle=\sqrt{p_i}|\psi_i\rangle$, $\rho=\sum_i|\psi_i'\rangle\langle\psi_i'|$ and $|\nu_i\rangle=\rho^{-1/2}|\psi_i'\rangle$, where $\rho^{-1/2}$ is taken over the non-zero eigenvalues of $\rho$; its success probability is $P^{\mathrm{PGM}}(E)=\sum_i p_i|\langle\nu_i|\psi_i\rangle|^2$. Then
--
--   $$
--   P^{\mathrm{opt}}(E)^2\le P^{\mathrm{PGM}}(E)\le P^{\mathrm{opt}}(E).
--   $$
--
--   This is the basic tool for turning upper bounds on the PGM success probability into upper bounds on the success of every measurement, as in the state-identification lower bounds of quantum sample complexity.
--
--   **Formalization Note** $P^{\mathrm{opt}}$ is a real supremum over the POVMs with $m$ outcomes; under the hypotheses this set is nonempty and bounded by $1$, so the supremum is the source's maximum value. $\rho^{-1/2}$ is the continuous functional calculus of $x\mapsto(\sqrt x)^{-1}$, which is $0$ at $x=0$ in Lean, i.e. the pseudo-inverse square root.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 159, Theorem 7.3.1. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

/-- Arunachalam p.159–160, Theorem 7.3.1 (Barnum–Knill): for an ensemble
`E = {(p_i, |ψ_i⟩)}_{i ∈ [m]}` of `d`-dimensional pure states with `p_i ≥ 0`, `∑ p_i = 1`,
the optimal average success probability `P^opt(E) = max_M ∑ p_i ⟨ψ_i|M_i|ψ_i⟩` over
`m`-outcome POVMs and the PGM success probability `P^PGM(E) = ∑ p_i |⟨ν_i|ψ_i⟩|²`
(`|ν_i⟩ = ρ^{-1/2} √p_i |ψ_i⟩`, `ρ^{-1/2}` over the non-zero eigenvalues of
`ρ = ∑ p_i |ψ_i⟩⟨ψ_i|`) satisfy `P^opt(E)² ≤ P^PGM(E) ≤ P^opt(E)`. -/
theorem barnumKnill {m d : ℕ} (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Fin d))
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hψ : ∀ i, IsState (ψ i)) :
    optSuccess p ψ ^ 2 ≤ pgmSuccess p ψ ∧ pgmSuccess p ψ ≤ optSuccess p ψ := by
  sorry






end QAlgorithms.Arunachalam
