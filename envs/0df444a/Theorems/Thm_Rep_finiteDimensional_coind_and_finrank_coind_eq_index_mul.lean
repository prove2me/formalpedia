-- Prove2me | Theorems.Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul
-- name    : Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e8c7e524-83e3-5eb1-8320-90e917319796
-- title:
--   Finite-dimensionality and dimension of a coinduced representation
-- statement:
--   Let $k$ be a field and $G$ a group (both in the same universe), let $S \le G$ be a subgroup of finite index, i.e. carrying a `Subgroup.FiniteIndex` instance, and let $N$ be a $k$-linear representation of $S$ whose underlying $k$-vector space is finite-dimensional. Consider the representation of $G$ coinduced along the inclusion `S.subtype : S →* G`, namely `Rep.coind S.subtype N`, whose underlying space is the space of functions $f \colon G \to N$ satisfying $f(sg) = \rho_N(s)\,f(g)$ for all $s \in S$ and $g \in G$, with $k$-linear structure computed pointwise. The theorem asserts the conjunction of two facts: this coinduced representation is finite-dimensional over $k$, and its $k$-dimension is given by $$\dim_k \operatorname{coind}_{S}^{G} N = [G : S] \cdot \dim_k N,$$ where $[G:S]$ is `Subgroup.index`, the cardinality of the left coset space $G ⧸ S$. Both assertions are statements about the underlying $k$-vector space only; no compatibility with the $G$-action beyond the defining equivariance condition enters the conclusion.
--
--   This is the dimension count underlying Shapiro-type comparisons between the cohomology of $G$ on a coinduced module and that of the finite-index subgroup $S$ on $N$. It is used by [`Rep.exists_shortExact_coind_res`](thm.html#Rep.exists_shortExact_coind_res) and, through it, in [`groupCohomology.euler_poincare_identity_of_hypotheses`](thm.html#groupCohomology.euler_poincare_identity_of_hypotheses), where the multiplicativity of dimensions by the index supplies the numerical input to the Euler–Poincaré argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul {k G : Type u} [Field k] [Group G] (S : Subgroup G) [S.FiniteIndex]
    (N : Rep.{u} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) = S.index * Module.finrank k N := by sorry
