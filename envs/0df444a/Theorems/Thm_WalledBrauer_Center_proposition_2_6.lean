-- Prove2me | Theorems.Thm_WalledBrauer_Center_proposition_2_6
-- name    : WalledBrauer.Center.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:23.561997+00:00
-- url     : https://prove2.me/theorems/44c3fe06-c1e4-480c-bdf6-ce38038210a2
-- title:
--   Proposition 2.6 — the Jucys–Murphy elements of $B_{r,s}(\delta)$ commute
-- statement:
--   For all $1\le i,j\le r+s$, the Jucys–Murphy elements of the walled Brauer algebra $B_{r,s}(\delta)$ commute:
--
--   $$
--   L_iL_j=L_jL_i .
--   $$
--
--   Commutativity makes $p(L_1,\dots,L_{r+s})$ well defined for every polynomial $p$, independent of the order of the factors, and generates the commutative subalgebra in which the center is described.
--
--   **Formalization Note** Vertices are 0-based (`jm δ i` is $L_{i+1}$). Commutativity does not depend on the product convention.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 10, Proposition 2.6

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem proposition_2_6 (r s : ℕ) (δ : ℂ) (i j : Fin (r + s)) :
    jm δ i * jm δ j = jm δ j * jm δ i := by sorry
end WalledBrauer.Center
