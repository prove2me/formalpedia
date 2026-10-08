-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_isBase_iff_rank_eq_nullity_eq_zero
-- name    : WhitneyMatroid.Duality.isBase_iff_rank_eq_nullity_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:43:19.64273+00:00
-- url     : https://prove2.me/theorems/2f712106-a72a-4881-9e62-bc946338dead
-- title:
--   Theorem 7 — $B$ is a base iff $r(B)=r(M)$ and $n(B)=0$
-- statement:
--   Let $M$ be a matroid on a finite set of elements, with rank function $r$ and nullity $n(N)=\rho(N)-r(N)$, where $\rho(N)$ is the number of elements of $N$. A subset $B$ of $M$ is a base of $M$ if and only if
--
--   $$
--   r(B) = r(M),\qquad n(B) = 0 .
--   $$
--
--   In words: a base is exactly an independent set ($n(B)=0$) of full rank. Whitney uses this rank characterization of bases to pass from the rank identity (11.1) to statements about bases (Theorem 23).
--
--   **Formalization Note** The matroid is a Mathlib `Matroid` on a finite type with ground set the whole type; "base" is Mathlib's `IsBase`, which agrees with Whitney's (maximal independent set). $r(M)$ is the rank of the whole ground set; the nullity is computed in $\mathbb Z$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 515, Theorem 7

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 7 (p. 515): in a matroid `M` on a finite set of elements, `B` is a base if
and only if `r(B) = r(M)` and `n(B) = 0`. -/
theorem isBase_iff_rank_eq_nullity_eq_zero {α : Type*} [Finite α] (M : Matroid α)
    (hE : M.E = Set.univ) (B : Set α) :
    M.IsBase B ↔ (M.eRk B = M.eRk Set.univ ∧ WhitneyMatroid.Components.nullity M B = 0) := by sorry

end WhitneyMatroid.Duality
