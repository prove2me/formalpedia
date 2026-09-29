-- Prove2me | Theorems.Thm_RibetIrr_exists_dickson_eval_eq_of_span_ne_top
-- name    : RibetIrr.exists_dickson_eval_eq_of_span_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4a11b12b-7605-5d9a-a4ad-cd81dacd9063
-- title:
--   Dickson trace identity in the non-absolutely-irreducible case
-- statement:
--   Fix a prime $p$ and a natural number $N \neq 0$. Let $\mathcal{O}$ be a characteristic-zero discrete valuation domain, complete for the adic topology of its maximal ideal and with finite residue field, and let $K$ be its fraction field. Let $\rho$ consist of a finite free $\mathcal{O}$-module $V$ with $\operatorname{rank}_{\mathcal{O}} V = 2$ together with a monoid homomorphism $\sigma \mapsto \rho(\sigma)$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, to $\operatorname{End}_{\mathcal{O}}(V)$, adically continuous in the sense that for each $n$ some finite subextension $L/\mathbb{Q}$ of $\overline{\mathbb{Q}}$ has the property that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}^n V$ for all $v$. Assume: $p \in \mathfrak{m}$; for every prime $q \nmid N$ with $q \neq p$ and every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, $\rho(\sigma) = 1$ for all $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$; and the following dichotomy at $p$: for every field $L$ finite over $K$ with compatible $\mathcal{O}$- and $K$-algebra structures and every $L$-line $W \subseteq L \otimes_{\mathcal{O}} V$ stable under all base-changed $\rho(\sigma)$, there is an $n > 0$ such that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit and every $\sigma$ in the inertia image at $P$, either $(\rho(\sigma) \otimes L)^n$ fixes every element of $W$, or $(\rho(\sigma) \otimes L)^n v - v \in W$ for every $v \in L \otimes_{\mathcal{O}} V$. Let $a : \mathbb{N} \to \mathcal{O}$ and let $E_0$ be a finite set of naturals such that for every prime $\ell \notin E_0$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a non-unit and every $\sigma$ lying in the decomposition group of $A$ and inducing $x \mapsto x^{\ell}$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2 - a_{\ell}X + \ell$. Finally assume that the $K$-span of the base changes $\rho(\sigma) \otimes K$, $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, is not all of $\operatorname{End}_K(K \otimes_{\mathcal{O}} V)$. Then there exist $m \neq 0$ and a finite set $E$ of naturals such that for every prime $\ell \notin E$ one has $D_m(a_{\ell}; \ell) = \ell^m + 1$ in $\mathcal{O}$, where $D_m(\,\cdot\,; \ell)$ is the Dickson polynomial `dickson 1 (ℓ : 𝒪) m` of the first kind.
--
--   This is the reducible case of Ribet's analysis of a two-dimensional $p$-adic representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with prescribed Frobenius characteristic polynomials: if the image fails to span the full endomorphism algebra, the traces $a_\ell$ are constrained by a Dickson-polynomial identity expressing that the ratio of the two eigenvalue characters has finite order. It is used by [`RibetIrr.span_range_baseChange_eq_top_of_companion`](thm.html#RibetIrr.span_range_baseChange_eq_top_of_companion), where the identity is contradicted for a suitable prime and absolute irreducibility is thereby obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

open scoped TensorProduct

theorem RibetIrr.exists_dickson_eval_eq_of_span_ne_top
    (p : ℕ) [Fact p.Prime] (N : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (ρ : GaloisRepAdic 𝒪) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (hN : N ≠ 0)
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪 L] [Algebra K L] [IsScalarTower 𝒪 K L]
      [FiniteDimensional K L] (W : Submodule L (L ⊗[𝒪] ρ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (a : ℕ → 𝒪) (E₀ : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : 𝒪)))
    (hspan : Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) ≠ ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ E : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ E →
      (dickson 1 ((ℓ : 𝒪)) m).eval (a ℓ) = (ℓ : 𝒪) ^ m + 1 := by sorry
