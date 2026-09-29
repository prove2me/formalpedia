-- Prove2me | Theorems.Thm_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
-- name    : ResidualGaloisRep.not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/9c95866f-c055-5917-8599-b9a785acef16
-- title:
--   Absolutely irreducible residual representations are not Eisenstein
-- statement:
--   Let $p$ be a prime, let $k$ be a field and $k'$ a field of characteristic $p$, and let $\psi : k \to k'$ be a ring homomorphism. Let $\bar\rho$ be a residual Galois representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho : \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$ that is trivial on the subgroup fixing some finite-dimensional intermediate field of $\overline{\mathbb Q}/\mathbb Q$. Let $L \ge 1$ and let $\kappa : \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to (\mathbb Z/L)^\times$ be a monoid homomorphism satisfying $\sigma\mu = \mu^{\kappa(\sigma)}$ for every $\sigma$ and every $\mu \in \overline{\mathbb Q}$ with $\mu^L = 1$ (the exponent being the canonical representative of $\kappa(\sigma)$ in $\{0,\dots,L-1\}$). Let $c_1, c_2 : (\mathbb Z/L)^\times \to k'^\times$ be monoid homomorphisms, and assume that either $p \ne 2$ or $c_1 c_2 = 1$. Let $S_0$ be a finite set of natural numbers and let $\bar a_\ell \in k$ be given for every prime $\ell \notin S_0$. Assume that for every prime $\ell \notin S_0$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition subgroup of $A$ over $\mathbb Q$ acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\mathrm{charpoly}(\bar\rho(\sigma)) = X^2 - \bar a_\ell X + \ell$ in $k[X]$ and $\psi(\bar a_\ell) = c_1(\kappa(\sigma)) + \ell\, c_2(\kappa(\sigma))$ in $k'$. Then $\bar\rho$ is not absolutely irreducible: the base change $\overline{k} \otimes_k V$, with $\overline{k}$ an algebraic closure of $k$, has a Galois-stable submodule other than $\bot$ and $\top$.
--
--   This is the statement that a two-dimensional residual representation whose Frobenius traces are Eisenstein, i.e. of the form $c_1(\ell) + \ell\, c_2(\ell)$ for two characters of $(\mathbb Z/L)^\times$ composed with the mod-$L$ cyclotomic character, cannot be absolutely irreducible. It is used in the contrapositive, to discard Eisenstein maximal ideals when Galois representations are attached to homomorphisms out of Hecke rings, in [`CuspForm.TWLevel.HeckeRing.exists_galoisRepAdic_of_algHom`](thm.html#CuspForm.TWLevel.HeckeRing.exists_galoisRepAdic_of_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
    {k k' : Type} [Field k] [Field k'] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (ρbar : ResidualGaloisRep k) (ψ : k →+* k')
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (c₁ c₂ : (ZMod L)ˣ →* k'ˣ) (h2 : p ≠ 2 ∨ c₁ * c₂ = 1)
    (S₀ : Finset ℕ) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k))
    (heis : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ψ (abar ℓ hℓ hℓS) = (c₁ (κ σ) : k') + (ℓ : k') * (c₂ (κ σ) : k')) :
    ¬ ρbar.IsAbsolutelyIrreducible := by sorry
