-- Prove2me | Theorems.Thm_ResidualGaloisRep_unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd
-- name    : ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/a73a9517-1650-5d97-8275-ceeaf6aa6cc6
-- title:
--   Flat classes are ordinary unit classes at p
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p$ an odd prime, and let $\bar\rho$ be a residual representation over $k$: a two-dimensional $k$-vector space $V$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k V$ that is trivial on the fixing subgroup of some finite extension of $\mathbb Q$. Let $V_1\subseteq V$ be a $k$-line, and write $\sigma\mapsto\rho(\iota\sigma)$ for the action of the local group $\mathrm{Aut}_{\mathbb Q_p}(\overline{\mathbb Q_p})$ obtained by restricting along the local-to-global map $\iota$. Assume: $V_1$ is stable under all $\rho(\iota\sigma)$; for every $\sigma$ whose local automorphism lies in the inertia subgroup of the valuation subring of $\overline{\mathbb Q_p}$ one has $\rho(\iota\sigma)v-v\in V_1$ for all $v\in V$; and for every such inertial $\sigma$ and every $c\in\mathbb N$ with $\sigma\zeta=\zeta^c$ on all $\zeta$ with $\zeta^p=1$, $\rho(\iota\sigma)$ acts on $V_1$ as the scalar $c\in k$. Assume further that the zero cocycle for the restricted adjoint representation $\mathrm{ad}\,\bar\rho=\mathrm{End}_k V$ satisfies `IsLocallyFlatCocycleAd`, i.e. there is a finite flat cocommutative Hopf $\mathbb Z_p$-algebra $H$ and a bijection from the convolution group of $\mathbb Z_p$-algebra maps $H\to\overline{\mathbb Q_p}$ onto $V\times V$ carrying convolution to addition and the Galois action to the diagonal action $x\mapsto(\rho(\iota\sigma)x_1,\rho(\iota\sigma)x_2)$. Then, first, every $\sigma$ in the unit-root inertia set — inertial elements fixing all $p$-th roots of unity and fixing every $\beta$ of norm $1$ whose $p$-th power is fixed by all of inertia — acts trivially on $V$; and second, the span in $H^1$ of the classes of locally flat cocycles is contained in the span of the classes of cocycles $c$ that satisfy the predicate `IsOrdinaryCocycleAd` for $V_1$, are of finite level (there is a finite extension $F/\mathbb Q$ with $c(gs)=c(g)$ whenever $\iota s$ fixes $F$), and vanish on the unit-root inertia set.
--
--   This is the structural half of the ordinary flat case of Wiles' Proposition 1.9, as presented in Darmon–Diamond–Taylor: a flat first-order deformation of an ordinary $\bar\rho|_{G_p}$ is, up to a coboundary, ordinary of unit type, and the unit-root inertia acts trivially on the residual space. It feeds the dimension count for the flat local condition in [`ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd.lean

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

theorem ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd
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
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    (∀ σ ∈ ResidualGaloisRep.unitRootInertia p, ∀ v : ρbar.V,
        ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = v) ∧
      ρbar.localFlatClassesAd p ≤ ρbar.ordinaryUnitClassesAd p V₁ := by sorry
