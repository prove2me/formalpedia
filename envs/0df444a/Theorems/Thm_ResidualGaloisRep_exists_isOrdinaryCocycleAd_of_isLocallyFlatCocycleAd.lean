-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd
-- name    : ResidualGaloisRep.exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/6a87e247-28c7-59c9-bf49-feaf69e3b02e
-- title:
--   Flat cocycles are cohomologous to ordinary flat cocycles
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p$ an odd prime, and let $\bar\rho$ consist of a two-dimensional $k$-vector space $V$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k V$ that is trivial on the automorphisms fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$. Write $G_p$ for the group of $\mathbb Q_p$-automorphisms of the algebraic closure $\mathrm{PadicAlgCl}\,p$, mapped to the global Galois group by `primeLocalToGlobal`, and $I_p$ for the inertia subgroup of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20), viewed inside $G_p$. Let $V_1 \subseteq V$ be a $k$-line such that: $\rho(\sigma)V_1 \subseteq V_1$ for all $\sigma \in G_p$; $\rho(\sigma)v - v \in V_1$ for all $v \in V$ and all $\sigma \in I_p$; and, for $\sigma \in I_p$ and $c \in \mathbb N$ with $\sigma\zeta = \zeta^c$ for every $p$-th root of unity $\zeta$, one has $\rho(\sigma)v = c\,v$ for $v \in V_1$. Assume the zero cocycle is locally flat, i.e. `ρbar.IsLocallyFlatCocycleAd p 0` holds. Let $c$ be a $1$-cocycle of $G_p$ with values in the restriction to $G_p$ of the adjoint representation $\sigma \cdot f = \rho(\sigma) f \rho(\sigma)^{-1}$ on $\mathrm{End}_k V$, satisfying `ρbar.IsLocallyFlatCocycleAd p c`: there is a finite flat cocommutative Hopf algebra $H$ over $\mathbb Z_p$ and a bijection $e$ from the convolution group of $\mathbb Z_p$-algebra maps $H \to \mathrm{PadicAlgCl}\,p$ onto $V \times V$ which is additive, $e(fg) = e(f)+e(g)$, and transforms the natural $G_p$-action on points into $\sigma\cdot(x_1,x_2) = (\rho(\sigma)x_1,\ c(\sigma)\rho(\sigma)x_1 + \rho(\sigma)x_2)$. Then there is a $1$-cocycle $c'$ with the same image as $c$ under the projection `H1π` to $H^1$, again satisfying `ρbar.IsLocallyFlatCocycleAd p c'`, and ordinary with respect to $V_1$: $c'(\sigma)V_1 \subseteq V_1$ for all $\sigma \in G_p$, while for $\sigma \in I_p$ one has $c'(\sigma)V \subseteq V_1$ and $c'(\sigma)$ vanishes on $V_1$.
--
--   This is the step in Wiles' comparison of local deformation conditions at $p$ (Chapter 1, proof of Proposition 1.9) asserting that a finite flat first-order deformation of a finite flat representation which is ordinary at $p$ is itself ordinary, the argument resting on Raynaud's classification results for finite flat group schemes. It is used to prove that the space of locally flat classes in $H^1(G_p,\mathrm{ad}\,\bar\rho)$ is contained in the space of ordinary classes attached to the line $V_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) (V₁ : Submodule k ρbar.V) (hV₁ : Module.finrank k V₁ = 1)
    (hstab : ∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₁,
      ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v ∈ V₁)
    (hdisp : ∀ (σ : primeLocalGaloisGroup (pPrime p)),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ v : ρbar.V, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v - v ∈ V₁)
    (hcyc : ∀ (σ : primeLocalGaloisGroup (pPrime p)),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ c : ℕ,
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) →
          ∀ v ∈ V₁, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = (c : k) • v)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ c' : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)),
      (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c' =
          (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c ∧
        ρbar.IsLocallyFlatCocycleAd p c' ∧ ρbar.IsOrdinaryCocycleAd p V₁ c' := by sorry
