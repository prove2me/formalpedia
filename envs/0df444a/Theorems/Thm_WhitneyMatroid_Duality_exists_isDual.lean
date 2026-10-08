-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_exists_isDual
-- name    : WhitneyMatroid.Duality.exists_isDual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:44:21.895349+00:00
-- url     : https://prove2.me/theorems/eddd1bd0-6631-43df-8b89-25490c8e3942
-- title:
--   Theorem 22 — every matroid has a dual
-- statement:
--   Let $M$ be a matroid on a finite set of elements $e_1,\dots,e_n$. Then $M$ has a dual: there is a matroid $M'$ on a copy $e'_1,\dots,e'_n$ of the same elements such that, under the correspondence $e_i\leftrightarrow e'_i$, for every subset $N$ of $M$ with $N'$ the complement of the corresponding subset of $M'$,
--
--   $$
--   r(N') = r(M') - n(N).
--   $$
--
--   In contrast with graphs, where only planar graphs have duals, every matroid has one.
--
--   **Formalization Note** The matroid $M$ is a Mathlib `Matroid` on a finite type `α` with ground set all of `α`; the dual is sought as a matroid on the same type `α` with the identity correspondence, which is the same as Whitney's copy of the elements.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 522, Theorem 22

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 22 (p. 522): every matroid has a dual. Here: every matroid `M` whose ground
set is the whole finite type `α` has a dual `M′` on (a copy of) the same elements, the
correspondence being the identity. -/
theorem exists_isDual {α : Type*} [Finite α] (M : Matroid α) (hE : M.E = Set.univ) :
    ∃ M' : Matroid α, IsDualVia M M' (Equiv.refl α) := by sorry

end WhitneyMatroid.Duality
