-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_feasibleIb_iff_forall_mem_M
-- name    : SoysterInexactLP.Auxiliary.feasibleIb_iff_forall_mem_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:28.160134+00:00
-- url     : https://prove2.me/theorems/3faa9b58-18ae-4d5e-a9d8-e01aafd41a93
-- title:
--   x is feasible for (Ib) iff A·x ≦ b for all A ∈ M and x ≧ 0
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb R^m$ be nonempty convex sets, $b\in\mathbb R^m$, and let $M$ be the set of $m\times n$ matrices $(a_1,\dots,a_n)$ with $a_j\in K_j$ for every $j$. Then $x\in\mathbb R^n$ is feasible for (Ib) if and only if
--   $$A x\le b\quad\text{for every }A\in M,\qquad\text{and}\qquad x\ge 0.$$
--
--   This is the matrix form of the set-inclusive constraint of (Ib), from which the auxiliary linear program is derived.
--
--   **Formalization Note** Nonemptiness and convexity are the paper's standing assumptions and are kept although the equivalence does not need them.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1156 (PDF p. 4), sentence after the definition of M

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem feasibleIb_iff_forall_mem_M {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j)) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    FeasibleIb K b x ↔ (∀ A ∈ MSet K, A *ᵥ x ≤ b) ∧ 0 ≤ x := by sorry

end SoysterInexactLP.Auxiliary
