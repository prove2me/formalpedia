-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_theorem_4_5
-- name    : SuperTableaux.JacobiTrudi.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:25.951017+00:00
-- url     : https://prove2.me/theorems/9d8cec64-c0e2-4131-b9c2-f85a78be90ab
-- title:
--   Theorem 4.5, p. 23 — for infinite $\mathcal A,\mathcal B$: $S^{\mathcal A/\mathcal B}_\lambda=\det(S^{\mathcal A/\mathcal B}_{\lambda_i-i+j})_{1\le i,j\le n}$
-- statement:
--   Let $\mathcal A$ and $\mathcal B$ be **infinite** linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$, and $\lambda=(\lambda_1\ge\cdots\ge\lambda_n)\in\mathbb Z^n_+$. Then
--   $$S^{\mathcal A/\mathcal B}_\lambda=\det\Big(S^{\mathcal A/\mathcal B}_{\lambda_i-i+j}\Big)_{1\le i,j\le n}$$
--   in $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$, where $S^{\mathcal A/\mathcal B}_\lambda$ is the generating function (3.14) of A/B-semistandard tableaux of shape $\lambda$ and the entries $S^{\mathcal A/\mathcal B}_k$, $k\in\mathbb Z$, are the characters of A/B-semistandard tableaux of level one (nonzero also for $k<0$).
--
--   This is the paper's Jacobi–Trudi type formula. Under the identification of Theorem 5.2 it gives a determinant formula for the characters of the irreducible quasi-finite highest weight modules of $\widehat{\mathfrak{gl}}_{\infty|\infty}$ parametrised by $\lambda$ (Corollary 5.4).
--
--   **Formalization Note** The ring $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$ is `MvPowerSeries (A ⊕ B) ℤ`: the variable `Sum.inl a` is $x_a$ and the variable `Sum.inr b` is the symbol $x_b^{-1}$, so a monomial with exponent vector $m$ is $\prod_a x_a^{m(a)}\prod_b (x_b^{-1})^{m(b)}$; this is literally a power-series ring in the symbols $x_a$ and $x_b^{-1}$. A/B-tableaux are encoded in cut coordinates (see the definitions item). The determinant is Mathlib's `Matrix.det` over the commutative ring `MvPowerSeries (A ⊕ B) ℤ`; rows and columns are $0$-indexed and $\lambda_i-i+j$ is computed in $\mathbb Z$ (the shift by one in $i$ and $j$ cancels). The hypothesis that $\mathcal A$ and $\mathcal B$ are infinite is the paper's.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 23, Theorem 4.5

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem theorem_4_5 {A B : Type*} [LinearOrder A] [Countable A] [Infinite A]
    [LinearOrder B] [Countable B] [Infinite B] (oddA : A → Bool) (oddB : B → Bool)
    (n : ℕ) (hn : 0 < n) (la : GenPartition n) :
    charAB oddA oddB la =
      (Matrix.of fun i j : Fin n =>
        charAB1 oddA oddB (la.1 i - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))).det := by sorry
end SuperTableaux.JacobiTrudi
