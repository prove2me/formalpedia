-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_rank_eq_nullity_of_isDual
-- name    : WhitneyMatroid.Duality.rank_eq_nullity_of_isDual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:43:43.669809+00:00
-- url     : https://prove2.me/theorems/ba3f6dbf-baf4-44a0-a793-69dd6dfcbc42
-- title:
--   Theorem 20 — a dual has rank $n(M)$ and nullity $r(M)$
-- statement:
--   Let $M$ and $M'$ be matroids on finite sets of elements, with ranks $r$ and nullities $n$, and suppose $M'$ is a dual of $M$ in the sense of (11.1). Then
--
--   $$
--   r(M') = n(M),\qquad n(M') = r(M).
--   $$
--
--   The rank and the nullity of the whole matroid exchange roles under duality; for a planar graph this is the exchange of the cyclomatic number and the rank of the cycle space between a graph and its dual.
--
--   **Formalization Note** "Dual" is `IsDual`, i.e. (11.1) for some one-to-one correspondence between the elements; ranks are `eRk` converted to integers, and all four quantities are integers.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 522, Theorem 20

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 20 (p. 522): if `M′` is a dual of `M`, then `r(M′) = n(M)` and
`n(M′) = r(M)`. -/
theorem rank_eq_nullity_of_isDual {α β : Type*} [Finite α] [Finite β] {M : Matroid α}
    {M' : Matroid β} (h : IsDual M M') :
    ((M'.eRk Set.univ).toNat : ℤ) = WhitneyMatroid.Components.nullity M Set.univ ∧
      WhitneyMatroid.Components.nullity M' Set.univ = ((M.eRk Set.univ).toNat : ℤ) := by sorry

end WhitneyMatroid.Duality
