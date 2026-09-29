-- Prove2me | Theorems.Thm_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le
-- name    : ResidualGaloisRep.finiteDimensional_ordinaryUnitClassesAd_and_finrank_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/28214325-fc19-52e2-baae-8b71690c553b
-- title:
--   Dimension bound for ordinary unit classes in H¹(ℚₚ,ad ρ̄)
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $k$ of characteristic $p$, and let $\bar\rho$ be a residual representation over $k$: a $k$-vector space $V$ of dimension $2$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k V$ that factors through the fixing subgroup of some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$. Let $V_1 \subseteq V$ be a $k$-line. Write $G_p$ for the group of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure $\overline{\mathbb{Q}}_p$, mapped into the global Galois group by `primeLocalToGlobal`, and let $I_p \subseteq G_p$ be the inertia subgroup attached to the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) over $\mathbb{Q}_p$. Assume: (i) $\rho(\sigma)V_1 \subseteq V_1$ for all $\sigma \in G_p$; (ii) $(\rho(\sigma)-1)V \subseteq V_1$ for all $\sigma \in I_p$; (iii) if $\sigma \in I_p$ and $c \in \mathbb{N}$ is such that $\sigma\zeta = \zeta^c$ for every $p$-th root of unity $\zeta$, then $\rho(\sigma)$ acts on $V_1$ as multiplication by $c$ in $k$; (iv) $\rho(\sigma) = \mathrm{id}_V$ for every $\sigma$ in [`ResidualGaloisRep.unitRootInertia p`](def/GaloisRep_OrdinaryUnitClasses.html#L17), the set of $\sigma \in I_p$ that fix all $p$-th roots of unity and fix every $\beta \in \overline{\mathbb{Q}}_p$ of norm $1$ whose $p$-th power is fixed by all of $I_p$. Let $\mathrm{ad}\,\bar\rho$ be $\mathrm{End}_k V$ with the action $\sigma \cdot f = \rho(\sigma) f \rho(\sigma)^{-1}$, restricted to $G_p$. Then the $k$-span in $H^1(G_p, \mathrm{ad}\,\bar\rho)$ of the classes of those $1$-cocycles $c$ which satisfy the predicate [`ResidualGaloisRep.IsOrdinaryCocycleAd`](def/GaloisRep_OrdinaryUnitClasses.html#L25) for $p$ and $V_1$, are of finite level (there is a finite subextension $F/\mathbb{Q}$ with $c(gs) = c(g)$ whenever $s \in G_p$ maps into the fixing subgroup of $F$), and vanish on `unitRootInertia p`, is finite-dimensional over $k$, of dimension at most $\dim_k (\mathrm{ad}\,\bar\rho)^{G_p} + 1$.
--
--   This is the ordinary half of the local bound $\dim H^1_{\mathrm{ord}} \le \dim H^0 + 1$ at the prime $p$ in Wiles' computation of local deformation conditions (Chapter 1, Proposition 1.9), here for the unit-root-inertia-trivial classes. It feeds the corresponding bound for the local flat classes in the ordinary case, [`ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary), and thence the dimension counts for the Selmer groups governing the deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le.lean

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

theorem ResidualGaloisRep.finiteDimensional_ordinaryUnitClassesAd_and_finrank_le
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
    (hunit : ∀ σ ∈ ResidualGaloisRep.unitRootInertia p, ∀ v : ρbar.V,
      ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = v) :
    FiniteDimensional k (ρbar.ordinaryUnitClassesAd p V₁) ∧
      Module.finrank k (ρbar.ordinaryUnitClassesAd p V₁) ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants + 1 := by sorry
