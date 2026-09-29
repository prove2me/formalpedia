-- Prove2me | Theorems.Thm_ValuationSubring_inertiaCharacter_eq_one_of_cyclotomic_eq_one
-- name    : ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/131f6250-79f2-5291-8299-3ed3249ecbf6
-- title:
--   Inertia character at q of exponent q-1 trivial when cyc(σ)=1
-- statement:
--   Let $R$ be a commutative ring, $q$ a prime number, and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $q$ lying in the non-units of $P$ (the predicate `LiesOverPrime`). Write $I_P$ for `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup. Let $\xi : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to R^{\times}$ be a function such that: $\xi(\sigma\tau) = \xi(\sigma)\xi(\tau)$ for all $\sigma, \tau \in I_P$; $\xi(\sigma) = 1$ whenever $\sigma \in I_P$ satisfies $\sigma(z)z^{-1} - 1 \in P^{\mathrm{nonunits}}$ for every $z \neq 0$ in $\overline{\mathbb{Q}}$; $\xi(\sigma)^{q-1} = 1$ for all $\sigma \in I_P$; and there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\xi(\sigma) = 1$ for every $\sigma \in I_P$ fixing $L$ pointwise. Let $\mathrm{cyc} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to (\mathbb{Z}/q)^{\times}$ be a group homomorphism satisfying $\sigma(\mu) = \mu^{(\mathrm{cyc}\,\sigma).\mathrm{val}}$ for every $\sigma$ and every $\mu \in \overline{\mathbb{Q}}$ with $\mu^{q} = 1$. Then for $\sigma \in I_P$ with $\mathrm{cyc}(\sigma) = 1$ one has $\xi(\sigma) = 1$.
--
--   This is the statement that a character of the inertia group at $q$ whose exponent divides $q-1$ is captured by the mod $q$ cyclotomic character, the level-one fundamental character of tame inertia: it vanishes on the kernel of $\mathrm{cyc}$ restricted to inertia. It is used in the construction of the inertia character attached to an adic Galois representation with cyclotomic determinant, via [`GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular`](thm.html#GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_inertiaCharacter_eq_one_of_cyclotomic_eq_one.lean

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing Polynomial

theorem ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one
    {R : Type} [CommRing R] {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hwild : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ξ σ = 1)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ (q - 1) = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1) :
    ξ σ = 1 := by sorry
