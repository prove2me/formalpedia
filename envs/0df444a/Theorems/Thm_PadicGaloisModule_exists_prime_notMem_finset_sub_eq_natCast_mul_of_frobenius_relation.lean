-- Prove2me | Theorems.Thm_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
-- name    : PadicGaloisModule.exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c909d213-9720-5c5f-b8fe-f16d28ce1817
-- title:
--   Abstract Ribet lemma: Hecke operators redundant modulo p
-- statement:
--   Let $p$ be a prime, $M\ge 1$ a natural number, $\mathbb{T}$ a (not necessarily commutative) ring, and $A$ a finitely generated free $\mathbb{Z}_p$-module. Assume given a ring homomorphism $\varphi:\mathbb{T}\to\operatorname{End}_{\mathbb{Z}_p}(A)$ satisfying: every $t\in\mathbb{T}$ with $\varphi(t)$ in $p\Lambda$, where $\Lambda$ is the $\mathbb{Z}_p$-submodule of $\operatorname{End}_{\mathbb{Z}_p}(A)$ spanned by the image of $\varphi$, is of the form $p\,t'$; a group homomorphism $\rho:\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\operatorname{End}_{\mathbb{Z}_p}(A)$ (into the multiplicative monoid) whose values commute with every $\varphi(t)$; and a continuity condition: for every $d$ there is a finite subextension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that each $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)a-a\in p^dA$ for all $a\in A$. Assume further elements $T_\ell\in\mathbb{T}$ for all primes $\ell\nmid M$, maps $e_1,e_2:\mathbb{Z}/M\to\mathbb{T}$, and $w\in\mathbb{N}$, such that for every prime $\ell\nmid M$ with $\ell\neq p$, every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $P$, and every $\sigma$ in the decomposition subgroup of $P$ over $\mathbb{Q}$ acting on the residue field of $P$ by $x\mapsto x^{\ell}$, the relation $\varphi(T_\ell)\rho(\sigma)=\varphi(e_1(\ell))\rho(\sigma)^2+\ell^{w}\,\varphi(e_2(\ell))$ holds in $\operatorname{End}_{\mathbb{Z}_p}(A)$. Then for every finite set $S\subseteq\mathbb{N}$ and every prime $\ell_0\nmid M$ with $\ell_0\neq p$ there is a prime $q\nmid M$ with $q\notin S$, $q\neq p$, $q\equiv\ell_0 \pmod M$, and $T_{\ell_0}-T_q=p\,t'$ for some $t'\in\mathbb{T}$.
--
--   This is Ribet's lemma on the redundancy of finitely many good Hecke operators, in an abstract form isolating the hypotheses actually used: a $p$-adic Galois lattice on which the ring acts faithfully modulo $p$ in the stated sense and on which an Eichler–Shimura type quadratic relation for Frobenius elements holds. It feeds into the comparison of eigenspaces of cusp forms away from a finite set of primes, via [`CuspForm.exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset`](thm.html#CuspForm.exists_twoCuspEigenspace_two_le_twoCuspEigenspace_empty_of_finset).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicGaloisModule_exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicGaloisModule.exists_prime_notMem_finset_sub_eq_natCast_mul_of_frobenius_relation
    {𝕋 : Type} [Ring 𝕋] (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    {A : Type} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
    (φ : 𝕋 →+* Module.End ℤ_[p] A)
    (hφ : ∀ t : 𝕋, φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
      ∃ t' : 𝕋, t = (p : 𝕋) * t')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋), ρ σ * φ t = φ t * ρ σ)
    (hcont : ∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A))
    (T : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → 𝕋) (e₁ e₂ : ZMod M → 𝕋) (w : ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          φ (T ℓ hℓ hℓM) * ρ σ =
            φ (e₁ (ℓ : ZMod M)) * (ρ σ * ρ σ) + ((ℓ : ℤ_[p]) ^ w) • φ (e₂ (ℓ : ZMod M)))
    (S : Finset ℕ) (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀M : ¬ ℓ₀ ∣ M) (hℓ₀p : ℓ₀ ≠ p) :
    ∃ (q : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M), q ∉ S ∧ q ≠ p ∧ (q : ZMod M) = (ℓ₀ : ZMod M) ∧
      ∃ t' : 𝕋, T ℓ₀ hℓ₀ hℓ₀M - T q hq hqM = (p : 𝕋) * t' := by sorry
