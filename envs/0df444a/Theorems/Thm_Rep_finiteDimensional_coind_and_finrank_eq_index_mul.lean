-- Prove2me | Theorems.Thm_Rep_finiteDimensional_coind_and_finrank_eq_index_mul
-- name    : Rep.finiteDimensional_coind_and_finrank_eq_index_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/6802cf77-80c0-54b3-b48d-ce437ae647a6
-- title:
--   Coinduction from a finite-index subgroup multiplies dimension by the index
-- statement:
--   Let $k$ be a field and $G$ a group, let $H \le G$ be a subgroup of finite index, and let $N$ be a $k$-linear representation of $H$ (an object of `Rep k H` with underlying $k$-module in the lowest universe) whose underlying $k$-vector space is finite-dimensional. Consider the coinduced representation `Rep.coind H.subtype N` of $G$ along the inclusion $H \hookrightarrow G$, whose underlying space is the space of functions $F : G \to N$ satisfying $F(hg) = \rho_N(h)\,F(g)$ for all $h \in H$, $g \in G$, with $G$ acting by right translation in the argument. The conclusion is the conjunction of two assertions: first, this coinduced representation is finite-dimensional over $k$; second, its $k$-dimension is given by $$\operatorname{finrank}_k\bigl(\mathrm{coind}_{H}^{G} N\bigr) = [G : H] \cdot \operatorname{finrank}_k N,$$ where $[G:H]$ is `Subgroup.index`, the cardinality of the left coset space, and the product is the product of natural numbers.
--
--   This is the standard dimension count for coinduction from a subgroup of finite index: the coinduced module is, as a $k$-vector space, a product of $[G:H]$ copies of $N$, indexed by the cosets, the finite-index hypothesis being what makes this product finite. It is used in the analysis of Euler characteristics of coinduced modules, and is cited here by [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finiteDimensional_coind_and_finrank_eq_index_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.finiteDimensional_coind_and_finrank_eq_index_mul
    {k : Type} [Field k] {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind H.subtype N) ∧
      Module.finrank k (Rep.coind H.subtype N) = H.index * Module.finrank k N := by sorry
