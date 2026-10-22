-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_eq_4_5
-- name    : SuperTableaux.JacobiTrudi.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:57.218234+00:00
-- url     : https://prove2.me/theorems/a2bf55b7-47e8-41d3-9912-626cee4e86d3
-- title:
--   (4.5), p. 24 — $h_\mu=\sum_{\lambda\ge\mu}K_{\lambda\mu}s_\lambda$ and $s_\lambda=\det(h_{\lambda_i-i+j})$ in $n$ variables
-- statement:
--   Let $n\ge1$ and $\lambda,\mu\in\mathscr P_n$ (partitions with at most $n$ parts). Let $s_\lambda(x_{[n]})$ be the Schur polynomial in $x_1,\dots,x_n$ and $h_k(x_{[n]})$ the complete symmetric polynomial of degree $k$, with $h_k=0$ for $k<0$, and $h_\mu=\prod_i h_{\mu_i}$. Then
--
--   1. $$h_\mu(x_{[n]})=\sum_{\substack{\lambda\in\mathscr P_n\\ \lambda\ge\mu}}K_{\lambda\mu}\,s_\lambda(x_{[n]});$$
--   2. $$s_\lambda(x_{[n]})=\det\big(h_{\lambda_i-i+j}(x_{[n]})\big)_{1\le i,j\le n}.$$
--
--   These are the classical $h$-expansion and Jacobi–Trudi identities (Macdonald), recalled in the paper and compared with the super analogues in the proof of Theorem 4.5.
--
--   **Formalization Note** $s_\lambda(x_{[n]})$ is defined as the paper does (Example 3.15 (1)): the generating function of semistandard tableaux of shape $\lambda$ with entries in $[n]$ (all of degree $0$), and $h_k=s_{(k)}$ for $k\ge0$. Both live in `MvPowerSeries (Fin n) ℤ`. The order $\ge$ is the lexicographic order of p. 23 (`toLex`). The sum in part 1 is a `HasSum` in the coefficientwise topology; only finitely many terms are nonzero. Indices $i-j$ are computed in $\mathbb Z$.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 24, (4.5)

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting
open scoped MvPowerSeries.WithPiTopology

namespace SuperTableaux.JacobiTrudi
theorem eq_4_5 (n : ℕ) (hn : 0 < n) (la mu : GenPartition n) (hla : ∀ i, 0 ≤ la.1 i)
    (hmu : ∀ i, 0 ≤ mu.1 i) :
    HasSum (fun nu : {nu : GenPartition n // (∀ i, 0 ≤ nu.1 i) ∧ toLex mu.1 ≤ toLex nu.1} =>
        (kostka nu.1 mu : ℤ) • schurN n nu.1) (hProdN n mu) ∧
      schurN n la = (Matrix.of fun i j : Fin n =>
        hN n (la.1 i - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))).det := by sorry
end SuperTableaux.JacobiTrudi
