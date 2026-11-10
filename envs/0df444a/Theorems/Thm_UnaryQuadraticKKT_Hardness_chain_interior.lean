-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_chain_interior
-- name    : UnaryQuadraticKKT.Hardness.chain_interior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:26.819201+00:00
-- url     : https://prove2.me/theorems/db9552b6-67c3-4a2f-a811-05ffd7279a2f
-- title:
--   Lemma 4.4 — strict interiority of every auxiliary coordinate
-- statement:
--   Let $k\ge1$, $s\in\{-1,1\}$, $m=k+2$ and $x,y\in[0,1]$, with $G$, $g$ and $u^*$ defined by Equations (6) and (15).
--   Then
--   $$u^*(x,y)\in(-1,1)^m.$$
--   The assertion includes all four endpoint pairs $x,y\in\{0,1\}$ and every intermediate pair, for either sign. It provides the strict interiority needed when comparing stationarity equations in the combined polynomial.
--
--   Differences from the source:
--   - encoding: m=k+2 auxiliary coordinates indexed from 1 through m, with u* named as the minimizer → Fin (k+2), with source index i+1, and the explicit vector from Equation (15); reason: integer exponents implement both negative powers exactly; the optimality and uniqueness assertions remain conclusions of Lemma 4.3
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Lemma 4.4, p.7, proof and Equation (15), p.8. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness

/-- Lemma 4.4, pp.7–8; endpoints x,y=0,1 are included. -/
theorem chain_interior (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ∀ i : Fin (k + 2), -1 < chainMinimizer k s x y i ∧
      chainMinimizer k s x y i < 1 := by sorry

end UnaryQuadraticKKT.Hardness
