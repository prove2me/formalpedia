-- Prove2me | Theorems.Thm_Rep_res_quotient_fixingSubgroup_smooth_and_unramified
-- name    : Rep.res_quotient_fixingSubgroup_smooth_and_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/481c5fb9-bf7b-5a51-9991-e52ae56e1c6b
-- title:
--   Inflated representations are smooth and unramified outside S
-- statement:
--   Fix a natural number $p$ that is prime, a finite set $S$ of rational primes and an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ (inside `AlgebraicClosure ℚ`). Assume that $L$ is unramified outside $S$ in the sense of the project's predicate: $L$ is finite-dimensional over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ — the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $A$ — is contained in the fixing subgroup $\Gamma_L$ of $L$. Assume also that $\Gamma_L$ is normal, and let $X$ be a representation over $\mathbb{Z}/p$ of the quotient group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})/\Gamma_L$. The conclusion concerns the restriction of $X$ along the quotient homomorphism, i.e. the inflation of $X$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and asserts two things: first, for every vector $m$ of the inflated representation there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every element of the fixing subgroup of $F$ fixes $m$; second, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $q$ as a nonunit, every element $g$ of the inertia subgroup of $A$ over $\mathbb{Q}$ acts on the inflated representation as the identity.
--
--   This is the elementary verification that a mod $p$ representation inflated from a finite Galois quotient $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})/\Gamma_L$, with $L$ unramified outside $S$, is smooth (every vector has open stabiliser, witnessed by a finite level) and unramified outside $S$. It supplies exactly the smoothness and unramifiedness hypotheses of the restricted-ramification cohomology machinery, and is used in the proof of [`groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two`](thm.html#groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_res_quotient_fixingSubgroup_smooth_and_unramified.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem Rep.res_quotient_fixingSubgroup_smooth_and_unramified
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hL : L.IsUnramifiedOutside S) [hn : L.fixingSubgroup.Normal]
    (X : Rep.{0} (ZMod p) ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)) :
    (∀ m : Rep.res (QuotientGroup.mk' L.fixingSubgroup) X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ s m = m) ∧
    (∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, (Rep.res (QuotientGroup.mk' L.fixingSubgroup) X).ρ g = 1) := by sorry
