-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_lemma_2_5
-- name    : SkutellaCQP.MaxCut.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:19.328921+00:00
-- url     : https://prove2.me/theorems/05a7dc43-12da-469e-b62a-967a49b8bc36
-- title:
--   Lemma 2.5, p. 12 — for identical machines āᵢⱼ = 1/m is an optimum of (CQP), unique if all wⱼ/pⱼ are distinct and positive
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines, and the convex quadratic program (CQP) in the form (11): minimize $Z_{CQP}(a)=\sum_j w_j\sum_{i=1}^m a_{ij}\big(\tfrac{1+a_{ij}}{2}p_j+\sum_{k\prec j}a_{ik}p_k\big)$ subject to $\sum_i a_{ij}=1$ for all $j$ and $a\ge0$. Let $\bar a_{ij}=1/m$ for all $i,j$. Then
--
--   1. $\bar a$ is feasible and is an optimum solution:
--   $$
--   Z_{CQP}(\bar a)\le Z_{CQP}(a)\qquad\text{for every feasible }a;
--   $$
--   2. if the ratios $w_j/p_j$, $j=1,\dots,n$, are pairwise different and positive, then $\bar a$ is the unique optimum: every feasible $a$ with $Z_{CQP}(a)=Z_{CQP}(\bar a)$ equals $\bar a$.
--
--   The lemma gives the optimum of the relaxation in closed form for identical machines; it yields the lower bound $Z^*\ge Z^*_{CQP}$ used for Theorem 2.6 b) and Theorem 6.1.
--
--   **Formalization Note** "Different and positive" ratios are cross-multiplied: $w_jp_k\ne w_kp_j$ for $j\ne k$, and $w_j>0$ for all $j$ (equivalent because $p>0$).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 12, Lemma 2.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Lemma 2.5, p. 12. For identical parallel machines the vector `ā_ij = 1/m` is an optimum
solution of (CQP); it is the unique optimum when the ratios `w_j/p_j` are pairwise different and
positive. -/
theorem lemma_2_5 {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hm : 0 < m) :
    SkutellaCQP.NoRel.Feasible (abar m n) ∧
    (∀ a : Fin m → Fin n → ℝ, SkutellaCQP.NoRel.Feasible a →
      ZCQP p w (abar m n) ≤ ZCQP p w a) ∧
    ((∀ j k, j ≠ k → w j * p k ≠ w k * p j) → (∀ j, 0 < w j) →
      ∀ a : Fin m → Fin n → ℝ, SkutellaCQP.NoRel.Feasible a →
        ZCQP p w a = ZCQP p w (abar m n) → a = abar m n) := by sorry

end SkutellaCQP.MaxCut
