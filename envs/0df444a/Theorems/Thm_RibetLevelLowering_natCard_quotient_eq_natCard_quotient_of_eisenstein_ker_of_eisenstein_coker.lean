-- Prove2me | Theorems.Thm_RibetLevelLowering_natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker
-- name    : RibetLevelLowering.natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2c2eedb6-72c4-5502-a71c-77e4d1ce4680
-- title:
--   Equal 𝔪-coinvariant counts from Eisenstein kernel and cokernel
-- statement:
--   Work over the polynomial ring $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ in indeterminates `heckeGen` $\ell$ indexed by the primes, written `HeckeAlg`. Let $X$ and $\Psi$ be additive commutative groups carrying $\mathbb{T}$-module structures, let $\theta \colon X \to \Psi$ be $\mathbb{T}$-linear, let $\eta \in \mathbb{T}$, and let $S$ be a finite set of primes. Two hypotheses are imposed for all primes $\ell \notin S$: first, every $x \in \ker\theta$ satisfies $(X_\ell - (\ell + 1))\cdot x = \eta \cdot y$ for some $y \in X$; second, every $\psi \in \Psi$ satisfies $(X_\ell - (\ell + 1))\cdot \psi = \theta(x)$ for some $x \in X$. Let $\mathfrak{m} \subset \mathbb{T}$ be a maximal ideal which is not eventually Eisenstein, i.e. there is no finite set $S'$ of primes with $X_\ell - (\ell+1) \in \mathfrak{m}$ for all $\ell \notin S'$, and assume $\eta \in \mathfrak{m}$. The conclusion is that the quotients $X/\mathfrak{m}X$ and $\Psi/\mathfrak{m}\Psi$, where $\mathfrak{m}X$ denotes $\mathfrak{m} \cdot \top$, have equal cardinality in the sense of `Nat.card` (so equality also holds, with common value $0$, when both quotients are infinite).
--
--   This is the commutative-algebra component of Ribet's level-lowering comparison: if the kernel of $\theta$ is Eisenstein modulo $\eta$ and the cokernel of $\theta$ is Eisenstein, then $\theta$ becomes an isomorphism after passing to $\mathfrak{m}$-coinvariants at a non-Eisenstein maximal ideal containing $\eta$. It is used in the comparison of character groups and component groups attached to a supersingular level datum, in the two `SSLevelDatum` finrank statements for the Hecke torsion of the ribbon component group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RibetLevelLowering_natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem RibetLevelLowering.natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker
    {X : Type*} [AddCommGroup X] [Module HeckeAlg X]
    {Ψ : Type*} [AddCommGroup Ψ] [Module HeckeAlg Ψ]
    (θ : X →ₗ[HeckeAlg] Ψ) (η : HeckeAlg) (S : Finset Nat.Primes)
    (hker : ∀ x : X, θ x = 0 → ∀ ℓ : Nat.Primes, ℓ ∉ S →
      ∃ y : X, (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x = η • y)
    (hcoker : ∀ (ψ : Ψ) (ℓ : Nat.Primes), ℓ ∉ S →
      ∃ x : X, (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • ψ = θ x)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (heis : ¬ IsEventuallyEisenstein 𝔪) (hη : η ∈ 𝔪) :
    Nat.card (X ⧸ (𝔪 • (⊤ : Submodule HeckeAlg X))) =
      Nat.card (Ψ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Ψ))) := by sorry
