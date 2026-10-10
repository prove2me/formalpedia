-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_lemma_A_1
-- name    : QuadMatIneq.Reduced.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:59.074982+00:00
-- url     : https://prove2.me/theorems/ca392381-2d08-47c5-9ab2-fba12e60f982
-- title:
--   Lemma A.1, p. 26 — AᵀA ⩽ BᵀB iff A = SB with SᵀS ⩽ I; strict version for full-column-rank B; S := AB† works
-- statement:
--   Let $A \in \mathbb R^{r\times q}$ and $B\in\mathbb R^{p\times q}$.
--
--   1. $A^\top A \le B^\top B$ if and only if there exists $S\in\mathbb R^{r\times p}$ such that
--   $$A = SB \quad\text{and}\quad S^\top S\le I. \tag{A.1}$$
--   2. If, in addition, $B$ has full column rank, then $A^\top A < B^\top B$ if and only if there exists $S\in\mathbb R^{r\times p}$ such that
--   $$A = SB\quad\text{and}\quad S^\top S < I. \tag{A.2}$$
--   3. If $A^\top A - B^\top B\le 0$, then $S := AB^\dagger$ satisfies (A.1); if $B$ has full column rank and $A^\top A - B^\top B < 0$, then $S := AB^\dagger$ satisfies (A.2).
--
--   This factorization lemma (a matrix form of Douglas' lemma) turns a quadratic matrix inequality into a linear equation with a contractive multiplier; it is the step behind the parameterization of QMI solution sets and the explicit gain formula of the mission.
--
--   **Formalization Note** The strict half of the "Moreover" is stated under the full-column-rank hypothesis of part (b), where it appears in the paper. $\le$ and $<$ are the Loewner order: $B^\top B - A^\top A$ is positive semidefinite, respectively positive definite.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma A.1, p. 26

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem lemma_A_1 {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]
    [DecidableEq ι] [DecidableEq ρ] [DecidableEq σ]
    (A : Matrix ρ ι ℝ) (B : Matrix σ ι ℝ) :
    ((Bᵀ * B - Aᵀ * A).PosSemidef ↔
        ∃ S : Matrix ρ σ ℝ, A = S * B ∧ (1 - Sᵀ * S).PosSemidef) ∧
    (B.rank = Fintype.card ι →
      ((Bᵀ * B - Aᵀ * A).PosDef ↔
        ∃ S : Matrix ρ σ ℝ, A = S * B ∧ (1 - Sᵀ * S).PosDef)) ∧
    ((-(Aᵀ * A - Bᵀ * B)).PosSemidef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosSemidef) ∧
    (B.rank = Fintype.card ι → (-(Aᵀ * A - Bᵀ * B)).PosDef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosDef) := by sorry

end QuadMatIneq.Reduced
