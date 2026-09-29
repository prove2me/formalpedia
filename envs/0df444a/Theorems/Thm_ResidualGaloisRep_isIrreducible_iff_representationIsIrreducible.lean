-- Prove2me | Theorems.Thm_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible
-- name    : ResidualGaloisRep.isIrreducible_iff_representationIsIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/98e8b881-537c-518d-b950-190c02b36ad3
-- title:
--   Stable-subspace irreducibility equals `Representation.IsIrreducible`
-- statement:
--   Let $k$ be a field and let $\rho$ be a residual Galois representation over $k$ in the sense of the project structure [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): a datum consisting of a type $V$ with the structure of a $k$-vector space with $\operatorname{finrank}_k V = 2$, a monoid homomorphism $\rho.\rho$ from the Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the algebraic closure of $\mathbb{Q}$ to $\operatorname{End}_k(V)$, together with the property [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17), namely that there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L$ finite-dimensional over $\mathbb{Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho.\rho\,\sigma = 1$. The theorem asserts the equivalence of two conditions. The first is the project predicate [`ResidualGaloisRep.IsIrreducible`](def/GaloisRep_Residual.html#L61): every $k$-submodule $W \subseteq V$ such that $\rho.\rho\,\sigma\,x \in W$ for all $\sigma$ in the Galois group and all $x \in W$ equals $\bot$ or $\top$. The second is Mathlib's `Representation.IsIrreducible` applied to $\rho.\rho$, read as a representation of the Galois group on $V$: the lattice of subrepresentations of $\rho.\rho$ is a simple order, i.e. it is nontrivial and each of its elements is $\bot$ or $\top$.
--
--   This is the compatibility statement between the project's stable-subspace formulation of irreducibility of a two-dimensional residual Galois representation and the general notion of an irreducible representation in Mathlib, where irreducibility is encoded as simplicity of the lattice of subrepresentations. It makes the general representation-theoretic API available to users of the residual-representation vocabulary, and is cited by [`ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible`](thm.html#ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isIrreducible_iff_representationIsIrreducible.lean

import Definitions.Def_GaloisRep_Residual
import Mathlib.RepresentationTheory.Irreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.isIrreducible_iff_representationIsIrreducible {k : Type} [Field k]
    (ρ : ResidualGaloisRep k) :
    ρ.IsIrreducible ↔ Representation.IsIrreducible ρ.ρ := by sorry
