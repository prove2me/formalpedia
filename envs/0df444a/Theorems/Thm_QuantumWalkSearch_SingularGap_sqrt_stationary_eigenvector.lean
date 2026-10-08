-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_sqrt_stationary_eigenvector
-- name    : QuantumWalkSearch.SingularGap.sqrt_stationary_eigenvector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:17.708696+00:00
-- url     : https://prove2.me/theorems/f02c5548-fe05-4119-8607-b01f4f40ba93
-- title:
--   §5, p. 17 — v = (√π_x) is a left and a right eigenvector of D(P) with eigenvalue 1
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ with stationary distribution $\pi$, let $D(P)=\operatorname{diag}(\pi)^{1/2}P\operatorname{diag}(\pi)^{-1/2}$, and let $v=(\sqrt{\pi_x})_{x\in X}$. Then
--   $$D(P)\,v=v\qquad\text{and}\qquad v^{\mathsf T}D(P)=v^{\mathsf T}.$$
--
--   The right-eigenvector identity uses that the rows of $P$ sum to one; the left-eigenvector identity uses the stationarity $\sum_x\pi_xp_{xy}=\pi_y$. Since $v$ has real entries, it follows that $D(P)^\dagger v=v$ as well, so $v$ is a left and right singular vector of $D(P)$ with singular value $1$; this is the singular value whose simplicity Proposition 3 asserts.
--
--   **Formalization Note** $D(P)v$ is the matrix–vector product and $v^{\mathsf T}D(P)$ the vector–matrix product, over $\mathbb C$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 17, Section 5 (restated in the proof of Proposition 3, p. 20)

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem sqrt_stationary_eigenvector {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) :
    discriminant P π *ᵥ (sqrtStationary π).ofLp = (sqrtStationary π).ofLp ∧
      (sqrtStationary π).ofLp ᵥ* discriminant P π = (sqrtStationary π).ofLp := by sorry

end QuantumWalkSearch.SingularGap
