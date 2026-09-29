-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
-- name    : ResidualGaloisRep.exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4f8d1ab1-62e2-5a36-a65b-7eec200eae56
-- title:
--   Existence of a Taylor–Wiles prime detecting a cocycle
-- statement:
--   Let $k$ be a field and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L/\mathbb Q$ inside $\overline{\mathbb Q}$, finite over $\mathbb Q$, with $\bar\rho(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. Let $p$ be a prime, $n \in \mathbb N$, and let $\zeta \in \overline{\mathbb Q}$ be a primitive $p^n$-th root of unity. Let $R$ be a commutative ring and $M$ a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $R$ which is assumed smooth in the sense that some intermediate field $E/\mathbb Q$, finite over $\mathbb Q$, has its fixing subgroup acting trivially on $M$. Let $c$ be a $1$-cocycle of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ with values in $M$ which is likewise locally constant: for some finite intermediate field $F/\mathbb Q$ one has $c(gs) = c(g)$ for all $g$ and all $s$ in the fixing subgroup of $F$. Let $\sigma$ be an automorphism with $\sigma\zeta = \zeta$ whose characteristic polynomial on $V$ splits as $(X-\alpha)(X-\beta)$ with $\alpha \neq \beta$ in $k$, and assume $c(\sigma) \notin \mathrm{im}(M.\rho(\sigma) - 1)$. Then for every finite set $T$ of natural numbers there is a prime $q \notin T$ with $q \equiv 1 \pmod{p^n}$ such that: $\bar\rho$ is unramified at $q$, meaning $\bar\rho$ kills the inertia subgroup (transported into $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$) of every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$; for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$ and every $\varphi$ in the decomposition group of $P$ acting as $x \mapsto x^q$ on the residue field of $P$, the characteristic polynomial of $\bar\rho(\varphi)$ on $V$ is $(X-\alpha')(X-\beta')$ with $\alpha' \neq \beta'$ in $k$ (possibly different from the given $\alpha,\beta$); and the restriction in degree $1$ along the homomorphism `primeLocalToGlobal q` from $\mathrm{Gal}(\overline{\mathbb Q_q}/\mathbb Q_q)$ to $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, paired with the identity of the restricted representation, sends the class of $c$ in $H^1$ to a non-zero element.
--
--   This is the Chebotarev (Frobenius density) step in the construction of Taylor–Wiles primes, as in the proof of Theorem 2.49 of Darmon–Diamond–Taylor: a global element $\sigma$ trivial on $\mathbb Q(\zeta_{p^n})$, with regular semisimple residual image and not killing the class of $c$, is converted into an actual prime $q \equiv 1 \pmod {p^n}$ outside a prescribed finite set with the same three properties. It is stated for an arbitrary smooth coefficient module $M$ rather than for $\mathrm{ad}^0\bar\rho$, and is used by [`ResidualGaloisRep.exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S`](thm.html#ResidualGaloisRep.exists_taylorWilesPrime_map_ne_zero_of_mem_continuousH1S).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CategoryTheory groupCohomology ExtCitation

theorem ResidualGaloisRep.exists_taylorWilesPrime_map_H1_ne_zero_of_notMem_range
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {p : ℕ} [Fact p.Prime] {n : ℕ} {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {R : Type} [CommRing R] (M : Rep R (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hM : ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s ∈ E.fixingSubgroup, M.ρ s = 1)
    (c : cocycles₁ M)
    (hc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ g s, s ∈ F.fixingSubgroup → c (g * s) = c g)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσζ : σ ζ = ζ)
    {α β : k} (hαβ : α ≠ β) (hσ : LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hcσ : c σ ∉ LinearMap.range (M.ρ σ - 1))
    (T : Finset ℕ) :
    ∃ q : Nat.Primes, (q : ℕ) ∉ T ∧ (q : ℕ) ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β)) ∧
      (groupCohomology.map (primeLocalToGlobal q)
          (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom (H1π M c) ≠ 0 := by sorry
