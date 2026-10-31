-- Prove2me | Theorems.Thm_ParriloTheta_lemma_2_2
-- name    : ParriloTheta.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:01.145962+00:00
-- url     : https://prove2.me/theorems/ce74eb39-57ae-49b6-898f-a97ecec11c4b
-- title:
--   Lemma 2.2 — the cone $\mathcal K^{(1)}_n$ via (2.4) and via conditions (i)–(iv)
-- statement:
--   Let $M$ be a symmetric real $n\times n$ matrix. The following are equivalent:
--   1. $M\in\mathcal K^{(1)}_n$;
--   2. there are positive semidefinite matrices $P(i)$, $i\in[n]$, and scalars $c_{ijk}\ge0$ for $1\le i<j<k\le n$ with
--   $$
--   \Big(\sum_{i=1}^n x_i\Big)x^TMx=\sum_{i=1}^n x_i\,x^TP(i)x+\sum_{1\le i<j<k\le n}c_{ijk}\,x_ix_jx_k ;\qquad(2.4)
--   $$
--   3. there are matrices $P(i)$, $i\in[n]$, forming a $\mathcal K^{(1)}$-certificate for $M$: $P(i)\succeq0$, $P(i)_{ii}=M_{ii}$, $2P(i)_{ij}+P(j)_{ii}=2M_{ij}+M_{ii}$ for $i\ne j$, and $P(i)_{jk}+P(j)_{ik}+P(k)_{ij}\le M_{ij}+M_{ik}+M_{jk}$ for distinct $i,j,k$.
--
--   This is the working description of the first cone used throughout §6.
--
--   **Formalization Note** Stated as the conjunction of (1)⇔(2) and (1)⇔(3). The index set is a finite linearly ordered type, whose order gives $i<j<k$.
--
--   Differences from the source:
--   - encoding: M ∈ Sⁿ (the ambient space of the cones) → hypothesis M.IsSymm; reason: every matrix of the paper's cones is in Sⁿ; same statements
--   - encoding: [n] with 1 ≤ i < j < k ≤ n → a finite linearly ordered type ι; c : ι → ι → ι → ℝ used only on i < j < k; reason: Lean convention; same data
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 2.2 with eq. (2.4), p.5

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_IsK1Cert

open MvPolynomial

namespace ParriloTheta

/-- **Lemma 2.2: the cone `K^(1)`.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 2.2 with eq. (2.4), p.5:
"A matrix M belongs to the cone K(1)_n if and only if there exist matrices P(i) ⪰ 0 for i ∈ [n]
and scalars c_ijk ≥ 0 for 1 ≤ i < j < k ≤ n satisfying Equation (2.4). Equivalently, there exist
matrices P(i) ∈ Sⁿ for i ∈ [n] satisfying the following conditions: (i) P(i) ⪰ 0 for all i ∈ [n],
(ii) P(i)_ii = M_ii for all i ∈ [n], (iii) 2P(i)_ij + P(j)_ii = 2M_ij + M_ii for all i ≠ j ∈ [n],
(iv) P(i)_jk + P(j)_ik + P(k)_ij ≤ M_ij + M_ik + M_jk for all distinct i, j, k ∈ [n]."
(2.4): "(∑_{i=1}^n x_i) xᵀMx = ∑_{i=1}^n x_i xᵀP(i)x + ∑_{1≤i<j<k≤n} c_ijk x_i x_j x_k."

**Formalization Note.** `M` ranges over symmetric matrices (the ambient space `Sⁿ` of the
cones). The index set is a finite linearly ordered type `ι` (the order gives `i < j < k`);
`c` is a function on all triples, constrained and used only on `i < j < k`. Conditions
(i)–(iv) are `IsK1Cert M P`. -/
theorem lemma_2_2 {ι : Type*} [Fintype ι] [LinearOrder ι] (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (InK 1 M ↔ ∃ (P : ι → Matrix ι ι ℝ) (c : ι → ι → ι → ℝ),
        (∀ i, (P i).PosSemidef) ∧ (∀ i j k, i < j → j < k → 0 ≤ c i j k) ∧
        (∑ i, (X i : MvPolynomial ι ℝ)) * (∑ j, ∑ k, C (M j k) * X j * X k) =
          ∑ i, X i * (∑ j, ∑ k, C (P i j k) * X j * X k) +
          ∑ i, ∑ j, ∑ k, (if i < j ∧ j < k then C (c i j k) * X i * X j * X k else 0)) ∧
    (InK 1 M ↔ ∃ P : ι → Matrix ι ι ℝ, IsK1Cert M P) := by sorry

end ParriloTheta
