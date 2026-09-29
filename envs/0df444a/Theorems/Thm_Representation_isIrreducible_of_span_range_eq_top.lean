-- Prove2me | Theorems.Thm_Representation_isIrreducible_of_span_range_eq_top
-- name    : Representation.isIrreducible_of_span_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/5129db33-b8a9-5fd6-9492-c1505963e720
-- title:
--   Representations spanning the endomorphism algebra are irreducible
-- statement:
--   Let $k$ be a field, $G$ a monoid and $V$ a $k$-vector space (an additive commutative group with a $k$-module structure), and let $\rho$ be a $k$-linear representation of $G$ on $V$, i.e. a monoid homomorphism from $G$ to the $k$-algebra $\operatorname{End}_k(V)$. Assume $V$ is nontrivial, i.e. contains a nonzero vector, and assume that the $k$-submodule of $\operatorname{End}_k(V)$ spanned by the set of operators $\{\rho(g) : g \in G\}$ (the range of the underlying function of $\rho$) is the whole of $\operatorname{End}_k(V)$. The conclusion is that $\rho$ is irreducible in Mathlib's sense: the lattice of subrepresentations of $\rho$ — $k$-submodules of $V$ stable under all the operators $\rho(g)$ — is a simple order, so $\bot \neq \top$ and every subrepresentation is either $0$ or $V$. Note that no finite-dimensionality of $V$, no algebraic closedness of $k$ and no commutativity of $G$ is assumed; the hypothesis is the spanning condition alone.
--
--   This is the converse half of Burnside's theorem on irreducible representations, the direction which holds over an arbitrary field and without finiteness assumptions. It is used to produce irreducibility, and after base change absolute irreducibility, of residual Galois representations from a spanning condition on the image: it is cited by [`ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible`](thm.html#ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible) and by [`RibetIrr.span_range_baseChange_eq_top_of_companion`](thm.html#RibetIrr.span_range_baseChange_eq_top_of_companion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_isIrreducible_of_span_range_eq_top.lean

import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Representation.isIrreducible_of_span_range_eq_top
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [Nontrivial V]
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) : ρ.IsIrreducible := by sorry
