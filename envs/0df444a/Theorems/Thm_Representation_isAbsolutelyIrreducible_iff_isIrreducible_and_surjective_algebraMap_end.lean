-- Prove2me | Theorems.Thm_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
-- name    : Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/33979837-8b26-5ba5-8ed8-81b5ac51dbe3
-- title:
--   Commutant criterion for absolute irreducibility of a representation
-- statement:
--   Let $k$ be a field, $G$ a group and $V$ a $k$-vector space, all three types lying in the same universe $u$, and assume $V$ is finite-dimensional over $k$; let $\rho$ be a representation of $G$ on $V$ over $k$. The theorem asserts the equivalence of two conditions. The first is the predicate [`Representation.IsAbsolutelyIrreducible`](def/Representation_AbsolutelyIrreducible.html#L27) for $\rho$ at universe $u$, which by definition says: for every type $k'$ in the universe $u$, every field structure on $k'$ and every $k$-algebra structure on it, the base-changed representation $k' \otimes_k \rho$ is irreducible in the sense of `Representation.IsIrreducible`. The second is the conjunction of two statements: that $\rho$ itself satisfies `Representation.IsIrreducible`, and that the structure map $k \to \operatorname{End}_{k[G]}(V)$, the algebra map into the endomorphism ring of $V$ regarded as a module over the monoid algebra `MonoidAlgebra k G` via $\rho$, is surjective — that is, every $k[G]$-equivariant endomorphism of $V$ is multiplication by a scalar. Note that the extension fields occurring in the definition of absolute irreducibility are restricted to the universe of $k$, $G$ and $V$; no algebraic closure is invoked, and $V$ is an abstract finite-dimensional space rather than a column space $k^n$.
--
--   This is the Schur–Burnside commutant criterion: absolute irreducibility is equivalent to irreducibility together with a commutant reduced to the scalars. It is the form in which absolute irreducibility of a residual representation is verified or used in the project, and it is cited in the construction of Hecke eigensystems on cuspidal cohomology and in the analysis underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.lean

import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end {k G V : Type u} [Field k]
  [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) :
  Representation.IsAbsolutelyIrreducible.{u} ρ ↔
    ρ.IsIrreducible ∧ Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule)) := by sorry
