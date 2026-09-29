-- Prove2me | Theorems.Thm_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
-- name    : ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bf70e4ff-b1d9-5f54-a9e0-d5a83ed5aa2c
-- title:
--   Inertia character factors through the p^k-quotient of (ℤ/q)^×
-- statement:
--   Let $R$ be a commutative local ring, let $q$ and $p$ be primes, suppose the image of $p$ in $R$ lies in the maximal ideal, and let $k$ be a natural number with $p^{k+1}\nmid q-1$. Let $P$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` lying over $q$, in the sense that $q$ is a non-unit of $P$, and write $I_P$ for `P.inertiaSubgroupIn ℚ`, the subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ obtained as the image of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup. Let $\xi$ be an arbitrary function from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $R^\times$ which is multiplicative on $I_P$ (i.e. $\xi(\sigma\tau)=\xi(\sigma)\xi(\tau)$ for $\sigma,\tau\in I_P$) and satisfies $\xi(\sigma)-1\in\mathfrak m_R$ for $\sigma\in I_P$. Let $\mathrm{cyc}$ be a group homomorphism to $(\mathbb Z/q)^\times$ such that $\sigma\mu=\mu^{\mathrm{cyc}(\sigma)}$ for every $\sigma$ and every $\mu$ with $\mu^q=1$ (the exponent being the canonical representative of $\mathrm{cyc}(\sigma)$ in $\{0,\dots,q-1\}$), and assume $\xi(\sigma)=1$ whenever $\sigma\in I_P$ and $\mathrm{cyc}(\sigma)=1$. Finally let $\pi_\Delta\colon(\mathbb Z/q)^\times\to\mathrm{Multiplicative}(\mathbb Z/p^k)$ be a surjective homomorphism. Then there is a homomorphism $\chi\colon\mathrm{Multiplicative}(\mathbb Z/p^k)\to R^\times$ with $\xi(\sigma)=\chi(\pi_\Delta(\mathrm{cyc}\,\sigma))$ for all $\sigma\in I_P$.
--
--   This is the step asserting that a residually trivial inertia character which is trivial on $I_P\cap\ker(\mathrm{cyc})$ factors through the diamond quotient $\Delta=\mathbb Z/p^k$ of $(\mathbb Z/q)^\times$, as in Darmon–Diamond–Taylor Lemma 2.44. It is used in the construction of inertia characters for an adic Galois representation with cyclotomic determinant, [`GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular`](thm.html#GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_Deformations_TameDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
    {R : Type} [CommRing R] [IsLocalRing R] {q : ℕ} (hq : q.Prime) {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : ℕ} (hk : ¬ p ^ (k + 1) ∣ q - 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hone : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (ξ σ : R) - 1 ∈ IsLocalRing.maximalIdeal R)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (hker : ∀ σ ∈ P.inertiaSubgroupIn ℚ, cyc σ = 1 → ξ σ = 1)
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ) :
    ∃ χ : Multiplicative (ZMod (p ^ k)) →* Rˣ, ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ = χ (πΔ (cyc σ)) := by sorry
