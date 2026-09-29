-- Prove2me | Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible
-- name    : Representation.span_range_eq_top_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4f307a68-0723-55ee-966a-fd6bd93561c9
-- title:
--   Burnside spanning for absolutely irreducible representations
-- statement:
--   Let $k$ be a field, $G$ a group and $V$ a $k$-vector space, all three types in one and the same universe, with $V$ finite-dimensional over $k$, and let $\rho$ be a $k$-linear representation of $G$ on $V$, i.e. a monoid homomorphism from $G$ to the $k$-algebra $\mathrm{End}_k(V)$ of $k$-linear endomorphisms of $V$. Assume $\rho$ is absolutely irreducible in the sense of the project's class [`Representation.IsAbsolutelyIrreducible`](def/Representation_AbsolutelyIrreducible.html#L27): for every type $k'$ in that same universe carrying a field structure and a $k$-algebra structure, the base-changed representation $k' \otimes \rho$ of $G$ on $k' \otimes_k V$ is irreducible. The conclusion is that the $k$-submodule of $\mathrm{End}_k(V)$ spanned by the set of values $\{\rho(g) : g \in G\}$ is the whole of $\mathrm{End}_k(V)$; equivalently, the image of $\rho$ spans the full endomorphism algebra over $k$. No hypothesis of algebraic closedness on $k$ is imposed, absolute irreducibility taking its place.
--
--   This is Burnside's spanning theorem in its absolutely irreducible form over an arbitrary base field, stated for an abstract finite-dimensional representation rather than for matrices. It supplies the spanning input used in the irreducibility arguments of the Ribet-style package, being cited by [`RibetIrr.exists_dickson_eval_eq_of_span_ne_top`](thm.html#RibetIrr.exists_dickson_eval_eq_of_span_ne_top) and [`RibetIrr.span_range_baseChange_eq_top_of_companion`](thm.html#RibetIrr.span_range_baseChange_eq_top_of_companion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Representation.span_range_eq_top_of_isAbsolutelyIrreducible {k G V : Type u} [Field k] [Group G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [Representation.IsAbsolutelyIrreducible.{u} ρ] :
  Submodule.span k (Set.range ρ) = ⊤ := by sorry
