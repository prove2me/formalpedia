-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_k_copy_bound
-- name    : QuantumWalkSearch.PhaseReflection.k_copy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:47:47.771211+00:00
-- url     : https://prove2.me/theorems/f355aadc-f79d-4685-aed6-28c0a4717cb2
-- title:
--   Proof of Theorem 6 — after $k$ phase estimations the all-zero-estimate component $\psi_0$ has $\|\psi_0\|\le2^{-k}\|\psi\|$, and $\|(R(P)+\mathrm{Id})|\psi\rangle|0^{ks}\rangle\|=2\|\psi_0\|$
-- statement:
--   Let $P$ be an ergodic and reversible Markov chain on a finite set $X$ with stationary distribution $\pi$, $k\ge0$ an integer, $s=\lceil\log_2(2\pi/\Delta(P))\rceil$, $V$ the $k$-fold repeated phase estimation of $W(P)$ and $R(P)=V^\dagger F_{\neq0}V$ the circuit of Theorem 6. For a vector $|\psi\rangle\in\mathcal H$ write
--   $$|\psi_0\rangle=\Pi_0\,V|\psi\rangle|0^{ks}\rangle$$
--   for the component of $V|\psi\rangle|0^{ks}\rangle$ on which the phase estimate is zero in each of the $k$ ancilla registers. Then:
--
--   1. if $|\psi\rangle\in\mathcal A+\mathcal B$ and $\langle\pi|\psi\rangle=0$, then $\|\psi_0\|\le 2^{-k}\,\|\psi\|$;
--   2. for every $|\psi\rangle\in\mathcal H$, $\big\|(R(P)+\mathrm{Id})\,|\psi\rangle|0^{ks}\rangle\big\| = 2\,\|\psi_0\|$.
--
--   Together with Theorem 5 and the single-copy bound, these are the two steps that give property 3 of Theorem 6.
--
--   **Formalization Note** The paper decomposes "$|\psi\rangle|0^{ks}\rangle$" into $|\psi_0\rangle+|\psi_1\rangle$ and writes $R(P)|\psi\rangle|0^{ks}\rangle=|\psi_0\rangle-|\psi_1\rangle$, which conflates the state before and after the final reversal $V^\dagger$. Here the decomposition is of $V|\psi\rangle|0^{ks}\rangle$, and the identity of part 2 uses that $V$ is unitary. The bound is homogeneous in $\psi$ ($\psi$ is a vector, not necessarily a unit state).
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 10, proof of Theorem 6 (unnumbered: "With k repetitions of the phase estimation, we can therefore decompose |ψ⟩|0^{ks}⟩ into a sum |ψ0⟩ + |ψ1⟩ ... whose norm is at most 2^{1−k}")

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit

namespace QuantumWalkSearch.PhaseReflection

/-- Proof of Theorem 6, p. 10: for an ergodic reversible chain and `ψ ∈ A + B` orthogonal to `|π⟩`,
after the `k`-fold phase estimation `V` the component `ψ₀` of `V|ψ⟩|0^{ks}⟩` with all `k` estimates
zero has norm at most `2^{−k}‖ψ‖`; and for every `ψ`, `‖(R(P) + Id)|ψ⟩|0^{ks}⟩‖ = 2‖ψ₀‖`. -/
theorem k_copy_bound {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (πd : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (herg : P.IsPrimitive)
    (hπ : IsStationaryDist P πd) (hrev : IsReversible P πd) (k : ℕ) :
    (∀ ψ ∈ spaceA P ⊔ spaceB P πd, inner ℂ (piState P πd) ψ = 0 →
      ‖Matrix.toEuclideanLin (zeroAncillaProj (precision (phaseGap P πd)) k)
          (Matrix.toEuclideanLin
            (repeatedPhaseEstimation (walkMatrix P πd) (precision (phaseGap P πd)) k)
            (tensorZero ψ))‖ ≤ (2 : ℝ) ^ (-(k : ℤ)) * ‖ψ‖) ∧
    (∀ ψ : H X,
      ‖Matrix.toEuclideanLin (reflectionCircuit P πd k + 1) (tensorZero ψ)‖ =
        2 * ‖Matrix.toEuclideanLin (zeroAncillaProj (precision (phaseGap P πd)) k)
          (Matrix.toEuclideanLin
            (repeatedPhaseEstimation (walkMatrix P πd) (precision (phaseGap P πd)) k)
            (tensorZero ψ))‖) := by sorry

end QuantumWalkSearch.PhaseReflection
