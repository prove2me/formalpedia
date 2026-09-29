-- Prove2me | Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
-- name    : ValuationSubring.apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/7bf53b48-0447-5ea2-966a-5b38b4f6718b
-- title:
--   Trivial cyclotomic character on inertia fixes (q-1)-th roots of q
-- statement:
--   Let $q$ be a prime number and let $P$ be a valuation subring of $\mathbb{Q}^{\mathrm{alg}} =$ `AlgebraicClosure ℚ` which lies over $q$ in the sense of the project's predicate `LiesOverPrime`, i.e. the image of $q$ in $\mathbb{Q}^{\mathrm{alg}}$ is a non-unit of $P$. Let $\mathrm{cyc}$ be a group homomorphism from $\mathrm{Gal}(\mathbb{Q}^{\mathrm{alg}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of $\mathbb{Q}^{\mathrm{alg}}$, to $(\mathbb{Z}/q)^{\times}$, and assume that $\mathrm{cyc}$ is pinned down by the cyclotomic relation: for every automorphism $\sigma$ and every $\mu \in \mathbb{Q}^{\mathrm{alg}}$ with $\mu^{q} = 1$ one has $\sigma(\mu) = \mu^{n}$, where $n$ is the canonical natural-number representative of $\mathrm{cyc}(\sigma) \in \mathbb{Z}/q$. Let $\sigma$ be an automorphism belonging to `P.inertiaSubgroupIn ℚ`, that is, lying in the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup into the full automorphism group, and assume $\mathrm{cyc}(\sigma) = 1$. Then for every $\alpha \in \mathbb{Q}^{\mathrm{alg}}$ with $\alpha^{q-1} = q$ one has $\sigma(\alpha) = \alpha$.
--
--   This is the elementwise form, inside $\mathbb{Q}^{\mathrm{alg}}$ and for a chosen valuation subring above $q$, of the comparison between the level-one fundamental character of tame inertia at $q$, given by $\sigma(\varpi)/\varpi$ for $\varpi^{q-1} = q$, and the mod-$q$ cyclotomic character, reflecting the equality $\mathbb{Q}_q(\zeta_q) = \mathbb{Q}_q(\varpi)$. It is used in the proof of [`ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one`](thm.html#ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1)
    (α : AlgebraicClosure ℚ) (hα : α ^ (q - 1) = (q : AlgebraicClosure ℚ)) :
    σ α = α := by sorry
