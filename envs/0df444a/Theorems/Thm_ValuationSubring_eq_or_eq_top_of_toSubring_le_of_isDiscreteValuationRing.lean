-- Prove2me | Theorems.Thm_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
-- name    : ValuationSubring.eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/563729de-fcb3-59b7-9cfc-594663fb084e
-- title:
--   Discrete valuation subrings have no proper overrings
-- statement:
--   Let $K$ be a field and let $A$ be a valuation subring of $K$ whose underlying ring is a discrete valuation ring in the Mathlib sense, i.e. a local principal ideal domain that is not a field. Let $B$ be a subring of $K$ containing the underlying subring `A.toSubring` of $A$. Then either $B$ coincides with `A.toSubring`, or $B$ is the top subring of $K$, that is, all of $K$. Thus the only rings intermediate between a discrete valuation subring of $K$ and $K$ itself are the two trivial ones. Note that the conclusion is an equality of subrings of $K$, the first alternative being equality with the subring underlying the valuation subring $A$ rather than with $A$ as a valuation subring; no hypothesis beyond $A \subseteq B$ is placed on $B$ (in particular $B$ is not assumed to be a valuation subring, local, or a localisation of $A$).
--
--   This is the classical statement that a rank-one (here: discrete) valuation ring is maximal among proper subrings of its fraction field, the overrings of a valuation ring being exactly its localisations at primes and the spectrum of a discrete valuation ring consisting of $(0)$ and the maximal ideal. It is used in the analysis of full-level modular curves, where the results on existence of subalgebras of Drinfeld rings with prescribed localisation and formal smoothness properties invoke it to pin down a subring sandwiched between a discrete valuation subring and its fraction field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
    {K : Type} [Field K] (A : ValuationSubring K) [IsDiscreteValuationRing ↥A]
    (B : Subring K) (h : A.toSubring ≤ B) : B = A.toSubring ∨ B = ⊤ := by sorry
