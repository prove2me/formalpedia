-- Prove2me | Theorems.Thm_WalledBrauer_Center_lemma_2_11
-- name    : WalledBrauer.Center.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:08.681565+00:00
-- url     : https://prove2.me/theorems/e0460b2f-6ecf-4be5-8007-1846101acd8f
-- title:
--   Lemma 2.11 — supersymmetric polynomials agree at two points iff their generating functions agree
-- statement:
--   Let $(a_1,\dots,a_r,b_1,\dots,b_s)$ and $(c_1,\dots,c_r,d_1,\dots,d_s)$ be points of $\mathbb C^{r+s}$. The following are equivalent:
--
--   1. $p(a_1,\dots,a_r,b_1,\dots,b_s)=p(c_1,\dots,c_r,d_1,\dots,d_s)$ for every supersymmetric polynomial $p\in S_{r,s}[x;y]$;
--   2. the rational functions in $z$ agree:
--   $$
--   \frac{\prod_{i=1}^r(1+a_iz)}{\prod_{j=1}^s(1-b_jz)}=\frac{\prod_{i=1}^r(1+c_iz)}{\prod_{j=1}^s(1-d_jz)} .
--   $$
--
--   The left-hand side is the generating function of the elementary supersymmetric polynomials evaluated at the point, so the lemma reduces separation by supersymmetric polynomials to a comparison of zeros and poles, which is how the content vectors of cell modules are separated (Lemma 2.12).
--
--   **Formalization Note** The equality of rational functions is stated cross-multiplied, as an identity in $\mathbb C[z]$: $\prod_i(1+a_iz)\prod_j(1-d_jz)=\prod_i(1+c_iz)\prod_j(1-b_jz)$. All four products are nonzero polynomials with constant term $1$, so this is equivalent to the equality of the quotients. Points are evaluated through `Sum.elim a b`, i.e. $x_i\mapsto a_i$, $y_j\mapsto b_j$.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 12, Lemma 2.11

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem lemma_2_11 (r s : ℕ) (a c : Fin r → ℂ) (b d : Fin s → ℂ) :
    (∀ p : MvPolynomial (Fin r ⊕ Fin s) ℂ, IsSupersymmetric p →
        eval (Sum.elim a b) p = eval (Sum.elim c d) p) ↔
      (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)) * (∏ j, (1 - Polynomial.C (d j) * Polynomial.X)) =
        (∏ i, (1 + Polynomial.C (c i) * Polynomial.X)) *
          (∏ j, (1 - Polynomial.C (b j) * Polynomial.X)) := by sorry
end WalledBrauer.Center
