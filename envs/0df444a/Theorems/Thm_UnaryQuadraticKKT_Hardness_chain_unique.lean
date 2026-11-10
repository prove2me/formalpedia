-- Prove2me | Theorems.Thm_UnaryQuadraticKKT_Hardness_chain_unique
-- name    : UnaryQuadraticKKT.Hardness.chain_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:26.380947+00:00
-- url     : https://prove2.me/theorems/245aab21-01b6-484a-b606-8406662fe1a7
-- title:
--   Lemma 4.3 — unique auxiliary global minimizer and unique KKT point
-- statement:
--   Let $k\ge1$, $s\in\{-1,1\}$, $m=k+2$ and $x,y\in[0,1]$, with $G$, $g$ and $u^*$ defined by Equations (6) and (15).
--   Then $u^*$ is feasible and globally minimizes $G_{x,y}$ over $[-1,1]^m$, every global minimizer equals $u^*$, $u^*$ is a box KKT point, and every box KKT point equals $u^*$:
--   $$\underset{u\in[-1,1]^m}{\operatorname{argmin}}G_{x,y}(u)=\operatorname{KKT}_{[-1,1]^m}(G_{x,y})=\{u^*(x,y)\}.$$
--   Both existence and both uniqueness claims are conclusions. This identifies the auxiliary vector that every target KKT point must use.
--
--   Differences from the source:
--   - encoding: m=k+2 auxiliary coordinates indexed from 1 through m, with u* named as the minimizer → Fin (k+2), with source index i+1, and the explicit vector from Equation (15); reason: integer exponents implement both negative powers exactly; the optimality and uniqueness assertions remain conclusions of Lemma 4.3
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Lemma 4.3, pp.6–7, and Equation (15), p.8. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness

/-- Lemma 4.3, pp.6–7; Eq. (15) names the vector, without assuming its optimality. -/
theorem chain_unique (k : ℕ) (hk : 1 ≤ k) (s : ℤ) (hs : s = -1 ∨ s = 1)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ChainGlobalMin k s x y (chainMinimizer k s x y) ∧
    (∀ u, ChainGlobalMin k s x y u → u = chainMinimizer k s x y) ∧
    IntervalKKT (fun _ => -1) (fun _ => 1) (chainValue k s x y)
      (chainMinimizer k s x y) ∧
    (∀ u, IntervalKKT (fun _ => -1) (fun _ => 1) (chainValue k s x y) u →
      u = chainMinimizer k s x y) := by sorry

end UnaryQuadraticKKT.Hardness
