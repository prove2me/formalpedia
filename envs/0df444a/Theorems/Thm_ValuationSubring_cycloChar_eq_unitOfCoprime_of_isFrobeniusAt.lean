-- Prove2me | Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
-- name    : ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/6c3eda45-68ba-5b1a-8194-c535d1bad0a1
-- title:
--   Mod-m cyclotomic character sends Frobenius at ℓ to ℓ
-- statement:
--   Let $m$ be a natural number and let $\mathrm{cyc}$ be a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to the unit group $(\mathbb{Z}/m)^{\times}$, assumed to compute the Galois action on $m$-th roots of unity in the following sense: for every automorphism $\sigma$ and every $\mu \in \overline{\mathbb{Q}}$ with $\mu^{m} = 1$ one has $\sigma(\mu) = \mu^{v}$, where $v$ is the canonical representative in $\{0,\dots,m-1\}$ of the residue class $\mathrm{cyc}(\sigma) \in \mathbb{Z}/m$. Let $\ell$ be a prime not dividing $m$. The assertion is that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in the nonunits of $A$, and every automorphism $\tau$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius at $A$ for $\ell$ — that is, $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and the induced action on the residue field of $A$ is $x \mapsto x^{\ell}$ — one has $\mathrm{cyc}(\tau) =$ the unit of $\mathbb{Z}/m$ determined by $\ell$ together with the coprimality of $\ell$ and $m$ coming from $\ell \nmid m$.
--
--   This is the classical computation of the mod-$m$ cyclotomic character on a Frobenius element at a prime $\ell \nmid m$, here phrased for an arbitrary homomorphism to $(\mathbb{Z}/m)^{\times}$ characterised by its action on $m$-th roots of unity. It is used when comparing a Galois representation with a twist by a character of $(\mathbb{Z}/m)^{\times}$ at Frobenius elements, and is cited in the construction of such a homomorphism on the absolute Galois group of $\mathbb{Q}$ and in the Hecke-character computations that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt.lean

import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
    (m : ℕ)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
        cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓm) := by sorry
