-- Prove2me | Theorems.Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary
-- name    : ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e12c2618-a479-5eae-b745-d1cdeefcc136
-- title:
--   Flat local bound for ordinary ρ̄ at p
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $k$ of characteristic $p$, and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a two-dimensional $k$-vector space $V$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k(V)$ factoring through some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$. Write $G_p = \overline{\mathbb Q_p} \simeq_{\mathbb Q_p} \overline{\mathbb Q_p}$ for the local group at $p$, acting on $V$ through the restriction homomorphism `primeLocalToGlobal`. Two hypotheses are imposed. First, the zero cocycle satisfies `IsLocallyFlatCocycleAd`: there is a finite flat cocommutative Hopf $\mathbb Z_p$-algebra $H$ and a bijection between the convolution group of $\mathbb Z_p$-algebra maps $H \to \overline{\mathbb Q_p}$ and $V \times V$ which is additive and intertwines the $G_p$-action on points with the diagonal action $\sigma \cdot (x_1,x_2) = (\rho(\sigma)x_1, \rho(\sigma)x_2)$. Second, $\bar\rho$ is ordinary at $p$: there is a $k$-line $V_1 \subseteq V$, stable under all of $G_p$, such that every $\sigma$ in the inertia subgroup of the valuation subring of $\overline{\mathbb Q_p}$ satisfies $\rho(\sigma)v - v \in V_1$ for all $v \in V$, and acts on $V_1$ by the scalar $c \bmod p$ whenever $\sigma\zeta = \zeta^{c}$ on the $p$-th roots of unity. The conclusion is that the $k$-span `localFlatClassesAd` of the classes in $H^1(G_p, \mathrm{ad}\,\bar\rho)$ represented by locally flat cocycles is finite-dimensional over $k$, of dimension at most $\dim_k (\mathrm{ad}\,\bar\rho)^{G_p} + 1$.
--
--   This is the local bound at $p$ for the flat deformation condition in the ordinary case, in the form $\dim_k H^1_{\mathrm{f}}(\mathbb Q_p, \mathrm{ad}\,\bar\rho) \le \dim_k H^0(\mathbb Q_p, \mathrm{ad}\,\bar\rho) + 1$, used in the computation of the tangent space of the flat deformation problem. It feeds the unconditional local bound [`ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_ordinary
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) (hflat : ρbar.IsLocallyFlatCocycleAd p 0)
    (hord : ∃ V₁ : Submodule k ρbar.V, Module.finrank k V₁ = 1 ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₁,
        ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v ∈ V₁) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
          ∀ v : ρbar.V, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v - v ∈ V₁) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ c : ℕ,
          (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) →
            ∀ v ∈ V₁, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = (c : k) • v)) :
    FiniteDimensional k (ρbar.localFlatClassesAd p) ∧
      Module.finrank k (ρbar.localFlatClassesAd p) ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants + 1 := by sorry
