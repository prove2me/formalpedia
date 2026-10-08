-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_isDualVia_iff_isBase_compl
-- name    : WhitneyMatroid.Duality.isDualVia_iff_isBase_compl
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:43:56.875667+00:00
-- url     : https://prove2.me/theorems/dac34881-81e3-424a-bf22-935f95d4c2ac
-- title:
--   Theorem 23 — duals iff bases correspond to base complements
-- statement:
--   Let $M$ and $M'$ be matroids on finite sets of elements and let $\sigma$ be a one-to-one correspondence between their elements. Then $M'$ is a dual of $M$ via $\sigma$ (identity (11.1) for every subset) if and only if bases in one correspond to base complements in the other: for every subset $B$ of $M$,
--
--   $$
--   B \text{ is a base of } M \iff (M' \setminus \sigma(B)) \text{ is a base of } M'.
--   $$
--
--   This turns the rank identity (11.1) into a statement about bases only; it is how Whitney proves Theorem 28, and it shows that a matroid's duals are exactly the copies of its usual dual matroid $M^*$.
--
--   **Formalization Note** Whitney's Theorem 23 reads "$M$ and $M'$ are duals if and only if there is a 1–1 correspondence such that bases in one correspond to base complements in the other." It is stated here for a fixed correspondence $\sigma$, as in Whitney's proof; the existential version follows by quantifying over $\sigma$ on both sides. Since $\sigma$ is a bijection, the displayed equivalence for all $B$ covers both directions of "bases in one correspond to base complements in the other". Both ground sets are the whole finite types.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 522–523, Theorem 23

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 23 (p. 522), for a fixed correspondence `σ`: `M` and `M′` (each with the whole
finite type as ground set) are duals via `σ` if and only if bases in one correspond to base
complements in the other: `B` is a base of `M` exactly when the complement of `σ(B)` is a base of
`M′`. -/
theorem isDualVia_iff_isBase_compl {α β : Type*} [Finite α] [Finite β] (M : Matroid α)
    (M' : Matroid β) (σ : α ≃ β) (hE : M.E = Set.univ) (hE' : M'.E = Set.univ) :
    IsDualVia M M' σ ↔ ∀ B : Set α, M.IsBase B ↔ M'.IsBase (Set.univ \ σ '' B) := by sorry

end WhitneyMatroid.Duality
