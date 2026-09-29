-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
-- name    : ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/6b3fed55-36ab-51d0-b1d2-4745e7f2cfa6
-- title:
--   Taylor–Wiles primes bounding first-order deformation classes
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain, complete for its maximal-ideal adic topology and with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, let $p$ be a prime with $p\neq 2$ and $p$ in the maximal ideal of $\mathcal O$, and let $\bar\rho$ be a residual representation over $k$: a two-dimensional $k$-space $V$ with a multiplicative map $\bar\rho\colon\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{End}_k V$ trivial on the fixing subgroup of some finite extension of $\mathbb Q$. Assume: $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline k$ has no Galois-stable submodule other than $\bot,\top$; the determinant condition `DetIsCyclotomic` holds, namely $p$ lies in the maximal ideal and $\det\bar\rho(\sigma)\equiv a \bmod p^n$ whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power; each characteristic polynomial $\mathrm{charpoly}(\bar\rho(\sigma))$ factors as $(X-\alpha)(X-\beta)$ with $\alpha,\beta\in k$; and for every field extension $K/k$ and every index-$2$ subgroup $G$ of the Galois group, every $K$-submodule of $(\bar\rho\otimes_k K)$'s space stable under $G$ is $\bot$ or $\top$. Let $S\supseteq S_{\min}$ be finite sets of naturals with $p\in S_{\min}$, all elements of $S$ prime, and such that a prime $q\neq p$ lies in $S_{\min}$ exactly when $\bar\rho$ is ramified at $q$ (some valuation subring over $q$ has an inertia element acting non-trivially). Give $k[\varepsilon]=\mathrm{DualNumber}\,k$ the $\mathcal O$-algebra structure through $\mathcal O\to k\to k[\varepsilon]$. The conclusion is the conjunction of two assertions of identical shape, one for the strict-ordinary local condition at $p$ and one for the flat condition. Each asserts: there is $r\in\mathbb N$ such that for every $n$ there is an injective family $q_1,\dots,q_r$ of primes, none in $S$, with $p^{n+1}\mid q_i-1$, such that for each $i$, each valuation subring $P$ of $\overline{\mathbb Q}$ in which $q_i$ is a non-unit and each $\varphi$ lying in the decomposition group of $P$ and inducing $x\mapsto x^{q_i}$ on its residue field, $\mathrm{charpoly}(\bar\rho(\varphi))=(X-\alpha)(X-\beta)$ with $\alpha\neq\beta$ in $k$; and moreover the $k$-dimension of the span inside $H^1(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q),\mathrm{ad}^0\bar\rho)$ — cohomology of the trace-zero part $\ker(\mathrm{tr})\subseteq\mathrm{End}_k V$ of the adjoint representation — of the set of classes $H^1\pi(c)$, for $1$-cocycles $c$ admitting the following first-order lift, is at most $r$: there is a representation $\rho_A$ over $k[\varepsilon]$ on a free rank-two module satisfying the strict-ordinary condition (respectively the flat condition) relative to $\mathcal O$, $p$ and $S_{\min}\cup\{q_1,\dots,q_r\}$ — cyclotomic determinant, strictly ordinary (respectively finite flat) at $p$, unramified at all primes outside that set — and with $\mathrm{charpoly}(\rho_A(\sigma))=(X-1)^2$ for $\sigma$ in inertia at each prime $q\in S_{\min}$, $q\neq p$, together with a homomorphism $\rho_d$ from the Galois group to the units of $\mathrm{DualNumber}(\mathrm{End}_k V)$ whose first component is $\bar\rho$, whose associated cochain $\sigma\mapsto\rho_d(\sigma)_{\mathrm{snd}}\,\bar\rho(\sigma)^{-1}$ equals $c(\sigma)$ in $\mathrm{End}_k V$, and for which there are bases of $\rho_A$'s module over $k[\varepsilon]$ and of $V$ over $k$ in which the matrix of $\rho_A(\sigma)$ corresponds, under `Matrix.dualNumberEquiv`, to the pair of matrices of the two components of $\rho_d(\sigma)$.
--
--   This is the Galois-cohomological half of the selection of Taylor–Wiles auxiliary primes: for each $n$ one produces a set $Q$ of $r$ primes congruent to $1$ modulo $p^{n+1}$, with distinct Frobenius eigenvalues for $\bar\rho$, for which the tangent space of the level-$Q$ deformation problem (strictly ordinary, respectively flat, at $p$) has $k$-dimension at most $r$, the bound $r$ being independent of $n$. It feeds the construction of a surjection from a power-series ring onto the level-$Q$ universal deformation ring, used in [`ResidualGaloisRep.exists_taylorWilesPrimes_mvPowerSeries_surjective_strictOrdinary`](thm.html#ResidualGaloisRep.exists_taylorWilesPrimes_mvPowerSeries_surjective_strictOrdinary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary.lean

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing groupCohomology TrivSqZeroExt

theorem ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : ResidueField 𝒪, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra (ResidueField 𝒪) K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (S Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S) (hS : ∀ q ∈ S, q.Prime)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q)) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    (∃ r : ℕ, ∀ n : ℕ, ∃ qv : Fin r → ℕ, Function.Injective qv ∧
      (∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ^ (n + 1) ∣ qv i - 1) ∧
      (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ (qv i) →
          ∃ α β : ResidueField 𝒪, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            (GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρA ∧
                ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q) ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) ≤ r) ∧
    (∃ r : ℕ, ∀ n : ℕ, ∃ qv : Fin r → ℕ, Function.Injective qv ∧
      (∀ i, (qv i).Prime ∧ qv i ∉ S ∧ p ^ (n + 1) ∣ qv i - 1) ∧
      (∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (qv i) →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ (qv i) →
          ∃ α β : ResidueField 𝒪, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            (GaloisRep.flatCondition 𝒪 p (Smin ∪ Finset.univ.image qv) ρA ∧
                ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q) ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) ≤ r) := by sorry
