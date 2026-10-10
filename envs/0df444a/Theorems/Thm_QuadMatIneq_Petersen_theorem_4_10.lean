-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_theorem_4_10
-- name    : QuadMatIneq.Petersen.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:32.252375+00:00
-- url     : https://prove2.me/theorems/32677d50-09ab-44be-b3d5-81566d49769b
-- title:
--   Theorem 4.10 (Strict matrix S-lemma), p. 13 — for $N\in\boldsymbol\Pi_{q,r}$, $N_{22}<0$: $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$ iff $M-\alpha N>0$, some $\alpha\geqslant0$
-- statement:
--   Let $M,N\in\mathbb S^{q+r}$ be symmetric matrices, partitioned as in (4.1) with upper-left blocks of size $q\times q$.
--
--   1. If there exists a real $\alpha\geqslant0$ such that $M-\alpha N>0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$.
--   2. Assume in addition that $N\in\boldsymbol\Pi_{q,r}$ and $N_{22}<0$. Then
--   $$\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)\iff \exists\,\alpha\geqslant0:\ M-\alpha N>0 .$$
--
--   This is the strict matrix S-lemma: a strict quadratic matrix inequality in $M$ holds on the whole solution set of a non-strict one in $N$ exactly when a single linear matrix inequality is feasible. It yields the strict form of Petersen's lemma.
--
--   **Formalization Note** The two block index sets are arbitrary finite types (sizes $q$ and $r$). No assumption $q\geqslant1$ is needed: for $q=0$ the statement remains true.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.10, p. 13

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI

namespace QuadMatIneq.Petersen
open Matrix
theorem theorem_4_10 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef) → ZSet N ⊆ ZPlus M) ∧
    (InPi N → (-N.toBlocks₂₂).PosDef →
      (ZSet N ⊆ ZPlus M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef)) := by sorry
end QuadMatIneq.Petersen
