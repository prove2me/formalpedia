-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_le_Abar_of_mem_M
-- name    : SoysterInexactLP.Auxiliary.le_Abar_of_mem_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:26.479885+00:00
-- url     : https://prove2.me/theorems/e0d1eb42-cd62-4cdc-99be-3ef732c3f450
-- title:
--   Every A ∈ M satisfies A ≦ Ā entrywise
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets with $\delta^*(e_i\mid K_j)<\infty$ for all $i,j$, and let $\bar A$ be the matrix with entries $\bar a_{ij}=\delta^*(e_i\mid K_j)$. Then every matrix $A=(a_1,\dots,a_n)$ with $a_j\in K_j$ for all $j$ satisfies
--   $$a_{ij}\le\bar a_{ij}\qquad\text{for all } i,j.$$
--
--   This is the first step of the proof of the THEOREM: $\bar A$ dominates every realisation of the uncertain constraint matrix.
--
--   **Formalization Note** Nonemptiness and finiteness make the real entries of $\bar A$ equal to the suprema; convexity is a standing assumption and unused.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), proof of THEOREM, first paragraph

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem le_Abar_of_mem_M {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : A ∈ MSet K) :
    ∀ i j, A i j ≤ Abar K i j := by sorry

end SoysterInexactLP.Auxiliary
