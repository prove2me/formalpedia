-- Prove2me | Theorems.Thm_QuantumWalkSearch_SingularGap_lemma_3
-- name    : QuantumWalkSearch.SingularGap.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:26.313425+00:00
-- url     : https://prove2.me/theorems/3ad73b40-4a26-4d14-8814-36df2f4004a5
-- title:
--   Lemma 3 — the singular values of D(P) lie in [0, 1]
-- statement:
--   Let $P=(p_{xy})_{x,y\in X}$ be an irreducible Markov chain on a finite state space $X$ with stationary distribution $\pi=(\pi_x)_{x\in X}$. Then every singular value $\sigma_i$ of the discriminant matrix
--   $$D(P)=\operatorname{diag}(\pi)^{1/2}\cdot P\cdot\operatorname{diag}(\pi)^{-1/2}$$
--   satisfies
--   $$0\le\sigma_i\le1 .$$
--
--   Equivalently, the largest singular value $\|D(P)\|$ is at most $1$. Together with the fact that $v=(\sqrt{\pi_x})$ is a singular vector with singular value $1$, this says that $1$ is the top singular value of $D(P)$, which is the setting of Proposition 3.
--
--   **Formalization Note** The singular values are Mathlib's sequence `LinearMap.singularValues` of $D(P)$ acting on $\mathbb C^X$, indexed by $i\in\mathbb N$ (the entries with $i\ge|X|$ are $0$, so the statement for all $i$ is the statement for the $|X|$ genuine singular values). The Markov chain is a row-stochastic real matrix and irreducibility is Mathlib's `Matrix.IsIrreducible` (nonnegative entries and a strongly connected graph of positive entries).
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 20, Lemma 3

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix

namespace QuantumWalkSearch.SingularGap

theorem lemma_3 {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π) :
    ∀ i : ℕ, 0 ≤ discriminantSingularValues P π i ∧ discriminantSingularValues P π i ≤ 1 := by sorry

end QuantumWalkSearch.SingularGap
