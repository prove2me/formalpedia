-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
-- name    : ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/a84c93ac-4d2f-532c-9395-0fa499f71a77
-- title:
--   Taylor–Wiles primes killing the dual Selmer group
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $k$ of characteristic $p$, and let $\bar\rho$ consist of a two-dimensional $k$-vector space $V$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k V$ factoring through a finite level. Assume: the base change of $\bar\rho$ to $\overline{k}$ is irreducible; for every $\sigma$ the characteristic polynomial of $\rho(\sigma)$ factors as $(X-\alpha)(X-\beta)$ with $\alpha,\beta\in k$; and for every field extension $K/k$, every subgroup $G$ of index $2$ and every $K$-submodule of the base change of $V$ to $K$ stable under $G$ is $\bot$ or $\top$. Let $\rho_0$ be a $\mathbb{Z}/p$-linear representation on $\ker(\mathrm{tr}_k\colon \mathrm{End}_k V\to k)$ agreeing pointwise with the adjoint action $\mathrm{ad}^0\bar\rho$. Let $S$ be a finite set of primes containing $p$ with $\bar\rho$ unramified at every $q\notin S$ (inertia at every valuation subring over $q$ acts trivially), and let $n\in\mathbb{N}$, $T$ a finite set of naturals. Then there is a finite set $Q$ of primes whose cardinality equals $\dim_{\mathbb{Z}/p}$ of `continuousH1S` $S$ of the dual of $\rho_0$ twisted by the mod $p$ cyclotomic character (the image in $H^1$ of the $S$-level cocycles), such that every $q\in Q$ satisfies $q\notin T$, $q\equiv 1 \pmod{p^n}$, $\bar\rho$ is unramified at $q$, and every Frobenius $\varphi$ at every place over $q$ has $\mathrm{charpoly}(\rho(\varphi))=(X-\alpha)(X-\beta)$ with $\alpha\neq\beta$; and any class in `continuousH1S` $(S\cup Q)$ of the same twisted dual whose restriction along the local-to-global map at each $q\in Q$ vanishes is itself zero.
--
--   This is the existence of Taylor–Wiles sets of auxiliary primes of depth $n$, as in Darmon–Diamond–Taylor Theorem 2.49(a)–(c): the set $Q$ has exactly the dimension of the unrestricted dual Selmer-type group $H^1_S$ as its cardinality, and imposing triviality at $Q$ kills that group. It feeds the bound on the dimension of the space of classes governing deformations in the Taylor–Wiles patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation

theorem ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hur : ∀ q : Nat.Primes, q ∉ S → ρbar.IsUnramifiedAt q)
    (n : ℕ) (T : Finset ℕ) :
    ∃ Q : Finset Nat.Primes,
      Q.card = Module.finrank (ZMod p)
        (continuousH1S S ((Rep.of ρ₀).dualTwist (cycloChar p))) ∧
      (∀ q ∈ Q, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
            ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      ∀ x ∈ continuousH1S (S ∪ Q) ((Rep.of ρ₀).dualTwist (cycloChar p)),
        (∀ q ∈ Q, (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) ((Rep.of ρ₀).dualTwist (cycloChar p)))) 1).hom x = 0) →
        x = 0 := by sorry
