-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_proposition_3
-- name    : QuantumWalkSearch.SingularGap.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:42.459033+00:00
-- url     : https://prove2.me/theorems/840e6cf9-d92a-417d-b470-9c6b4a4ba673
-- title:
--   Proposition 3 — with positive self-loops, D(P) has exactly one singular value equal to 1
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ such that
--   $$p_{xx}>0\qquad\text{for every }x\in X,$$
--   and let $\pi$ be its stationary distribution. Then the discriminant matrix
--   $$D(P)=\operatorname{diag}(\pi)^{1/2}\cdot P\cdot\operatorname{diag}(\pi)^{-1/2}$$
--   has exactly one singular value equal to $1$: among its $|X|$ singular values $\sigma_0\ge\sigma_1\ge\dots\ge\sigma_{|X|-1}$, counted with multiplicity,
--   $$\#\{\,i<|X| : \sigma_i=1\,\}=1 .$$
--
--   Combined with Lemma 3 (all singular values lie in $[0,1]$), this says that $D(P)$ has a non-zero singular value gap. The self-loop hypothesis cannot be dropped: there are ergodic chains whose discriminant has zero singular value gap. The result is what allows the quantum-walk search algorithm of the paper to be run with a non-reversible Markov chain, with the eigenvalue gap of $P$ replaced by the singular value gap of $D(P)$ (Theorem 8).
--
--   **Formalization Note** The chain is a row-stochastic real matrix, irreducible in the sense of Mathlib's `Matrix.IsIrreducible`; the stationary distribution is given as data (positive, summing to $1$, left $1$-eigenvector of $P$). The singular values are Mathlib's `LinearMap.singularValues` of $D(P)$ acting on $\mathbb C^X$, which lists the square roots of the eigenvalues of $D(P)^\dagger D(P)$ with multiplicity, so the count is the multiplicity of the singular value $1$. Reversibility is not assumed.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 17, Proposition 3 (proof pp. 20-21)

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem proposition_3 {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (hself : ∀ x : X, 0 < P x x) :
    ((Finset.range (Fintype.card X)).filter
        (fun i => discriminantSingularValues P π i = 1)).card = 1 := by sorry

end QuantumWalkSearch.SingularGap
