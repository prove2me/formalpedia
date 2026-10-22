-- Prove2me | Theorems.Thm_WalledBrauer_Center_corollary_2_9
-- name    : WalledBrauer.Center.corollary_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:20.946981+00:00
-- url     : https://prove2.me/theorems/c294cd05-56cc-467e-9332-8e8a23246f2e
-- title:
--   Corollary 2.9 — supersymmetric polynomials in $L_1,\dots,L_{r+s}$ are central
-- statement:
--   For every complex number $\delta$ and every supersymmetric polynomial $p\in S_{r,s}[x;y]$, the element
--
--   $$
--   p(L_1,\dots,L_{r+s})
--   $$
--
--   obtained by substituting $x_i\mapsto L_i$ and $y_j\mapsto L_{r+j}$ belongs to the center $Z(B_{r,s}(\delta))$ of the walled Brauer algebra. This is one inclusion of the main theorem (Theorem 3.5), and it holds without any semisimplicity assumption.
--
--   **Formalization Note** $p(L_1,\dots,L_{r+s})$ is `evalJM δ p`, which multiplies the factors of each monomial in increasing vertex order (the $L_k$ commute, Proposition 2.6). The center is `Subalgebra.center ℂ`, the same set for the platform's product and its opposite.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 11, Corollary 2.9

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem corollary_2_9 (r s : ℕ) (δ : ℂ) (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hp : IsSupersymmetric p) :
    evalJM δ p ∈ Subalgebra.center ℂ (B r s δ) := by sorry
end WalledBrauer.Center
