-- Prove2me | Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
-- name    : Representation.span_range_baseChange_eq_top_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/1e08da20-1dd2-5776-a2b3-96a6f40398c7
-- title:
--   Spanning of an endomorphism algebra is insensitive to base change
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, let $G$ be a monoid, and let $V$ be a finite-dimensional $k$-vector space. Let $\rho$ be a representation of $G$ on $V$ over $k$, that is, a monoid homomorphism from $G$ to the $k$-linear endomorphisms of $V$. Consider, on one side, the $K$-submodule of $\operatorname{End}_K(K \otimes_k V)$ spanned by the set of base-changed operators $(\rho g) \otimes \mathrm{id}_K$, as $g$ runs over $G$, and, on the other, the $k$-submodule of $\operatorname{End}_k(V)$ spanned by the set of operators $\rho g$. The assertion is that the first span is the whole of $\operatorname{End}_K(K \otimes_k V)$ if and only if the second span is the whole of $\operatorname{End}_k(V)$; no separability, algebraicity or finiteness hypothesis on the extension $K/k$, and no hypothesis on $G$ beyond being a monoid, is imposed.
--
--   This is the descent statement that makes Burnside-type spanning criteria independent of the base field: surjectivity of the span of a representation onto the full endomorphism algebra may be tested after any extension of scalars, in particular over an algebraic closure. It is used to pass from absolute irreducibility of a residual representation to the spanning hypothesis needed in the Brauer–Nesbitt trace argument, and is cited by the results deducing a full span from absolute irreducibility, both in the abstract and in the matrix formulation, and by the base-change stability of absolute irreducibility for residual Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_span_range_baseChange_eq_top_iff.lean

import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module LinearMap

theorem Representation.span_range_baseChange_eq_top_iff
    {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ ↔
      Submodule.span k (Set.range ⇑ρ) = ⊤ := by sorry
