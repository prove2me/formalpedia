-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_chain_exact
-- name    : UnaryQuadraticKKT.Hardness.chain_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:18.814226+00:00
-- url     : https://prove2.me/theorems/fbdea933-a4e4-4895-83dd-214ed52a902e
-- title:
--   Lemma 4.5 — exact minimized dyadic monomial
-- statement:
--   Let $k\ge1$, $s\in\{-1,1\}$, $m=k+2$ and $x,y\in[0,1]$, with $G$, $g$ and $u^*$ defined by Equations (6) and (15).
--   Then the equality of values is exact:
--   $$G(x,y,u^*(x,y))=g(x,y)=s2^{-k}xy.$$
--   There is no additive error, missing square term or change in sign. This identity supplies the exact dyadic coefficient represented by a chain, including when the factors are equal or constant when used later.
--
--   Differences from the source:
--   - encoding: m=k+2 auxiliary coordinates indexed from 1 through m, with u* named as the minimizer → Fin (k+2), with source index i+1, and the explicit vector from Equation (15); reason: integer exponents implement both negative powers exactly; the optimality and uniqueness assertions remain conclusions of Lemma 4.3
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Lemma 4.5, p.8. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness

/-- Lemma 4.5, p.8; both square terms and the sign are retained. -/
theorem chain_exact (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    chainValue k s x y (chainMinimizer k s x y) = chainMonomial k s x y := by sorry

end UnaryQuadraticKKT.Hardness
