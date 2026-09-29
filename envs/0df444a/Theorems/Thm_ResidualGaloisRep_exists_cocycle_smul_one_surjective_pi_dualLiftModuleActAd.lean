-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
-- name    : ResidualGaloisRep.exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/289333eb-d968-5214-92b3-8c720a70c8f5
-- title:
--   Dual-lift module of a scalar cocycle as equivariant quotient
-- statement:
--   Let $k$ be a field, $p$ a prime, and $\bar\rho$ a residual Galois representation over $k$, that is a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k V$ trivial on the automorphisms fixing some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$. Let $\ell$ be a prime with $\mathrm{char}\,k = \ell$, write $G_p$ for the group of $\mathbb{Q}_p$-algebra automorphisms of a fixed algebraic closure of $\mathbb{Q}_p$, and let $\chi\colon G_p \to \mathbb{Z}/\ell$ (written multiplicatively) be a surjective homomorphism. The assertion is the existence of a function $a\colon G_p \to k$ and a $1$-cocycle $c$ for the restriction along $G_p \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the adjoint representation $\sigma \mapsto (f \mapsto \bar\rho(\sigma) f \bar\rho(\sigma)^{-1})$ on $\mathrm{End}_k V$, such that $c(\sigma) = a(\sigma)\cdot \mathrm{id}_V$ for all $\sigma$, $a$ is not identically zero, $a(\sigma\tau) = a(\sigma) + a(\tau)$, and there is a surjective additive map $\pi\colon \mathrm{Map}(\mathbb{Z}/\ell, V) \to V \times V$ with $$\pi\bigl(i \mapsto \bar\rho(\sigma)(F(i - \chi(\sigma)))\bigr) = \bigl(\bar\rho(\sigma)v,\; c(\sigma)(\bar\rho(\sigma)v) + \bar\rho(\sigma)w\bigr), \quad (v,w) = \pi(F),$$ for all $\sigma \in G_p$ and all $F$, the right-hand side being the dual-lift action `dualLiftModuleActAd` attached to $c$.
--
--   The statement exhibits the dual-lift module attached to a non-trivial scalar (hence unramified, once $\chi$ is) $1$-cocycle of $\mathrm{ad}\,\bar\rho$ restricted to a decomposition group as a $G_p$-equivariant quotient of the permutation module $\mathrm{Map}(\mathbb{Z}/\ell, V)$ induced from the $\chi$-twist. It is used in the verification that such classes satisfy the local condition at $p$, via [`ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one`](thm.html#ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped TensorProduct

theorem ResidualGaloisRep.exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (χ : primeLocalGaloisGroup (pPrime p) →* Multiplicative (ZMod ℓ)) (hχ : Function.Surjective χ) :
    ∃ (a : primeLocalGaloisGroup (pPrime p) → k)
      (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))),
      (∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ =
          a σ • (1 : Module.End k ρbar.V)) ∧
      (∃ σ, a σ ≠ 0) ∧ (∀ σ τ, a (σ * τ) = a σ + a τ) ∧
      ∃ π : (ZMod ℓ → ρbar.V) →+ ρbar.V × ρbar.V, Function.Surjective π ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (F : ZMod ℓ → ρbar.V),
          π (fun i => ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (F (i - Multiplicative.toAdd (χ σ)))) =
            ρbar.dualLiftModuleActAd p c σ (π F) := by sorry
