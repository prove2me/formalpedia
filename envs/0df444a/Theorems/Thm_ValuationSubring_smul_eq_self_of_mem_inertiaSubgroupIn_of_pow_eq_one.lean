-- Prove2me | Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
-- name    : ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a4bd3958-0eb7-54d2-b3ff-71203b7ad73a
-- title:
--   Inertia fixes roots of unity of order prime to q
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$. Let $q$ be a prime natural number and assume that $A$ lies over $q$ in the sense that the image of $q$ in $L$ belongs to `A.nonunits`, i.e. $q$ lies in the maximal ideal of $A$. Let $\sigma$ be a $K$-algebra automorphism of $L$ belonging to `A.inertiaSubgroupIn K`, that is, to the image in $L \simeq_{\mathrm{alg}[K]} L$, under the inclusion of the decomposition subgroup of $A$, of the inertia subgroup of $A$; concretely, $\sigma$ stabilises $A$ and induces the identity automorphism of the residue field of $A$. Finally let $\zeta \in L$ and $m \in \mathbb{N}$ with $q \nmid m$ and $\zeta^m = 1$. The conclusion is that $\sigma \zeta = \zeta$. Note that $q \nmid m$ forces $m \neq 0$, so $\zeta$ is genuinely a root of unity of order prime to the residue characteristic.
--
--   This is the standard fact that inertia at a place of residue characteristic $q$ acts trivially on roots of unity of order prime to $q$, stated here for an arbitrary valuation subring of an arbitrary field extension rather than only for places of number fields. It is used in the analysis of the local behaviour at auxiliary primes of the Galois representations attached to Taylor–Wiles level structures, and is cited by the construction of Galois representations with prescribed local conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by sorry
