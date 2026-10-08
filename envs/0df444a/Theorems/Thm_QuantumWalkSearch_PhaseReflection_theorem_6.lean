-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_theorem_6
-- name    : QuantumWalkSearch.PhaseReflection.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:47:35.599605+00:00
-- url     : https://prove2.me/theorems/0ab94a2e-68db-436c-b3f8-71251ca9120b
-- title:
--   Theorem 6, properties 2–3 — $R(P)$ fixes $|\pi\rangle|0^{ks}\rangle$ and $\|(R(P)+\mathrm{Id})|\psi\rangle|0^{ks}\rangle\|\le2^{1-k}\|\psi\|$ for $\psi\in\mathcal A+\mathcal B$, $\psi\perp\pi$
-- statement:
--   Let $P$ be an ergodic and reversible Markov chain on a state space $X$ of size $n\ge2$, with stationary distribution $\pi$, quantum walk $W(P)$ and phase gap $\Delta(P)$. For an integer $k\ge0$ let $s=\lceil\log_2(2\pi/\Delta(P))\rceil$ and let $R(P)$ be the circuit on $\mathbb C^{X\times X}\otimes(\mathbb C^{2^s})^{\otimes k}$ obtained by applying the phase-estimation circuit $C(W(P))$ to $k$ ancilla registers, flipping the phase of every basis state with a non-zero estimate in some register, and reversing the phase estimation. Then:
--
--   1. $R(P)\,|\pi\rangle|0^{ks}\rangle=|\pi\rangle|0^{ks}\rangle$;
--   2. for every $|\psi\rangle\in\mathcal A+\mathcal B$ orthogonal to $|\pi\rangle$,
--   $$\big\|(R(P)+\mathrm{Id})\,|\psi\rangle|0^{ks}\rangle\big\|\ \le\ 2^{1-k}\,\|\psi\| .$$
--
--   So on $\mathcal A+\mathcal B$, with the ancillas initialised to $|0^{ks}\rangle$, $R(P)$ is within $2^{1-k}$ of the reflection $\mathrm{ref}(\pi)$ about $|\pi\rangle$. This is the diffusion operator of the quantum-walk search algorithm of §3.3: it replaces the costly exact reflection by $k$ phase estimations of the walk, which is the source of the $1/\sqrt\delta$ dependence of the search cost.
--
--   **Formalization Note** $R(P)$ is the explicit circuit of the proof (definition `reflectionCircuit`), not "some circuit with properties 2–3". **Reversibility** is the standing assumption of §3.2 (p. 8: "in the rest of this section, and in the next one, we assume that the classical Markov chain P is ergodic and reversible"); Theorem 6's own text says only "ergodic", but property 3 fails without it (if $D(P)$ has a second singular value $1$, $W(P)$ fixes a vector of $\mathcal A+\mathcal B$ orthogonal to $|\pi\rangle$). Property 2's premise "if $|\pi\rangle$ is the unique 1-eigenvector" holds under these hypotheses and is not assumed. "Ergodic" is `Matrix.IsPrimitive`. The explicit $s$ of the proof replaces "$s\in\log_2(1/\Delta(P))+O(1)$"; with the convention $\Delta(P)=\pi$ when $D(P)$ has no singular value in $(0,1)$, $s\ge1$. Property 1 (gate counts and calls to $c\text{-}W(P)$), the qubit count $2\lceil\log_2n\rceil+ks$ (the system register is $\mathbb C^{X\times X}$ rather than qubits) and uniformity are cost statements and are not formalized. $k=0$ is allowed (then $R(P)=\mathrm{Id}$ and the bound reads $2\|\psi\|$).
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 9, Theorem 6, properties 2 and 3 (proof pp. 9–10); standing assumption §3.2, p. 8

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit

namespace QuantumWalkSearch.PhaseReflection

/-- Theorem 6 (p. 9), properties 2 and 3, for the circuit `R(P)` of its proof, under the standing
assumption of §3.2 (p. 8) that `P` is ergodic and reversible. -/
theorem theorem_6 {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (πd : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (herg : P.IsPrimitive)
    (hπ : IsStationaryDist P πd) (hrev : IsReversible P πd)
    (hn : 2 ≤ Fintype.card X) (k : ℕ) :
    Matrix.toEuclideanLin (reflectionCircuit P πd k) (tensorZero (piState P πd)) =
      tensorZero (piState P πd) ∧
    ∀ ψ ∈ spaceA P ⊔ spaceB P πd, inner ℂ (piState P πd) ψ = 0 →
      ‖Matrix.toEuclideanLin (reflectionCircuit P πd k + 1) (tensorZero ψ)‖ ≤
        (2 : ℝ) ^ (1 - (k : ℤ)) * ‖ψ‖ := by sorry

end QuantumWalkSearch.PhaseReflection
