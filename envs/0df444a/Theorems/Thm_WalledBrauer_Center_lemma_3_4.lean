-- Prove2me | Theorems.Thm_WalledBrauer_Center_lemma_3_4
-- name    : WalledBrauer.Center.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:19.555423+00:00
-- url     : https://prove2.me/theorems/40afada9-e5ed-46ea-8a91-349e2861a0e4
-- title:
--   Lemma 3.4 ([20, Theorem 3.3]) — a point-separating subalgebra gives $p_1,\dots,p_n$ with $\det(p_i(j))\ne0$
-- statement:
--   Let $S$ be a $\mathbb C$-subalgebra of $\mathbb C[X_1,\dots,X_m]$, let $n\ge1$, and let $k_1,\dots,k_n\in\mathbb C^m$ be points, $k_i=(k_{i1},\dots,k_{im})$. Write $p(i)=p(k_{i1},\dots,k_{im})$. Assume that for all $1\le i\ne j\le n$ there is $p\in S$ with $p(i)\ne p(j)$. Then there are $p_1,\dots,p_n\in S$ with
--
--   $$
--   \det\bigl(p_i(j)\bigr)_{1\le i,j\le n}\ne0 .
--   $$
--
--   Applied to the supersymmetric polynomials and the content vectors of the simple modules, it yields central elements whose values on the simple modules form a nonsingular matrix, hence linearly independent central elements.
--
--   **Formalization Note** The matrix has rows indexed by the polynomials and columns by the points: entry $(i,j)$ is $p_i$ evaluated at $k_j$. Points are functions `Fin n → Fin m → ℂ`.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, pp. 16–17, Lemma 3.4 (after Li [20, Theorem 3.3])

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem lemma_3_4 (m n : ℕ) (hn : 0 < n) (S : Subalgebra ℂ (MvPolynomial (Fin m) ℂ))
    (k : Fin n → Fin m → ℂ)
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p ∈ S, eval (k i) p ≠ eval (k j) p) :
    ∃ P : Fin n → MvPolynomial (Fin m) ℂ,
      (∀ i, P i ∈ S) ∧ (Matrix.of fun i j => eval (k j) (P i)).det ≠ 0 := by sorry
end WalledBrauer.Center
