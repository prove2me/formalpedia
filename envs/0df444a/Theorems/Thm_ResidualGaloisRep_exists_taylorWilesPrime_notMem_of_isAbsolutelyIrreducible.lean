-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
-- name    : ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/f0cc901b-fcf1-59e0-ad0c-fe7567fb1057
-- title:
--   Existence of Taylor–Wiles primes of depth n outside a finite set
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, to $\mathrm{End}_k(V)$, which factors through a finite level in the sense that some intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $[L:\mathbb{Q}] < \infty$ has $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Assume $\bar\rho$ is absolutely irreducible, i.e. the only submodules of $\overline{k} \otimes_k V$ stable under all base-changed operators $\rho(\sigma)$ are $\bot$ and $\top$, and assume that for every $\sigma$ there are $\alpha, \beta \in k$ with $\mathrm{charpoly}(\rho(\sigma)) = (X-\alpha)(X-\beta)$. Let $p$ be a prime with $p \neq 2$, let $n$ be a natural number and $S$ a finite set of natural numbers. Then there is a prime $q \notin S$ with $q \equiv 1 \pmod{p^n}$ such that: $\bar\rho$ is unramified at $q$, meaning $\rho(\sigma) = 1$ for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ and every $\sigma$ in the image in the Galois group of the inertia subgroup of $A$ over $\mathbb{Q}$; and for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ and every $\varphi$ lying in the decomposition subgroup of $P$ over $\mathbb{Q}$ and acting on the residue field of $P$ by $x \mapsto x^{q}$, there exist $\alpha \neq \beta$ in $k$ with $\mathrm{charpoly}(\rho(\varphi)) = (X-\alpha)(X-\beta)$.
--
--   This is the existence statement for Taylor–Wiles primes of depth $n$ for a residual representation (the first assertion of Darmon–Diamond–Taylor, Theorem 2.49, in the form of Taylor–Wiles, Lemma 3 combined with a Chebotarev argument): arbitrarily many primes $q \equiv 1 \bmod p^n$, avoiding any prescribed finite set, at which $\bar\rho$ is unramified and $\bar\rho(\mathrm{Frob}_q)$ has distinct $k$-rational eigenvalues. It is used to produce finite sets of Taylor–Wiles primes whose cardinality matches the dimension of the relevant Selmer-type cohomology group, the input to the patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem ResidualGaloisRep.exists_taylorWilesPrime_notMem_of_isAbsolutelyIrreducible
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ q ≡ 1 [MOD p ^ n] ∧ ρbar.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ q →
          ∃ α β : k, α ≠ β ∧ LinearMap.charpoly (ρbar.ρ φ) = (X - C α) * (X - C β) := by sorry
