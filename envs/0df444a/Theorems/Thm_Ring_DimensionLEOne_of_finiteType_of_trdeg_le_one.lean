-- Prove2me | Theorems.Thm_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one
-- name    : Ring.DimensionLEOne.of_finiteType_of_trdeg_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c127db58-caf4-51ba-98e9-45ca52ac2a8b
-- title:
--   Finite-type domains of transcendence degree ≤ 1 are dimension ≤ 1
-- statement:
--   Let $k$ be a field and $B$ a commutative ring which is an integral domain, equipped with a $k$-algebra structure making it of finite type over $k$ (that is, $B$ is generated as a $k$-algebra by finitely many elements). Assume that the transcendence degree $\operatorname{trdeg}_k B$, taken as a cardinal, satisfies $\operatorname{trdeg}_k B \le 1$. The conclusion is `Ring.DimensionLEOne B`, i.e. every prime ideal of $B$ that is not the zero ideal is a maximal ideal; for the domain $B$ this is the assertion that its Krull dimension is at most one. Both $k$ and $B$ range over arbitrary universes.
--
--   This is the standard dimension theory of finitely generated algebras over a field, in the special case of transcendence degree at most one: such a domain is either a field or one-dimensional. It is used in the study of minimal primes above the maximal ideal of a subalgebra, in [`Subalgebra.mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin`](thm.html#Subalgebra.mem_minimalPrimes_map_maximalIdeal_of_not_isMaximal_of_fg_of_isAlgebraic_adjoin), where it rules out non-maximal nonzero primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ring_DimensionLEOne_of_finiteType_of_trdeg_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ring.DimensionLEOne.of_finiteType_of_trdeg_le_one
    (k : Type*) (B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (htr : Algebra.trdeg k B ≤ 1) : Ring.DimensionLEOne B := by sorry
