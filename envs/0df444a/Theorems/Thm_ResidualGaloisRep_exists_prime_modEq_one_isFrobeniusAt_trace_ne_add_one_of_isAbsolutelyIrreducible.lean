-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
-- name    : ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7ae35e90-9b58-5a60-b313-8340a08b4a80
-- title:
--   Absolutely irreducible residual representations are non-Eisenstein
-- statement:
--   Let $k$ be a field, $p$ a prime with $p \neq 2$, and suppose $k$ has characteristic $p$. Let $\rho$ be a residual Galois representation over $k$ in the sense of the project: a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\mathrm{End}_k V$, subject to the condition that $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that every automorphism fixing $L$ pointwise is sent to $1$. Assume $\rho$ is absolutely irreducible, meaning that after base change to $\mathrm{AlgebraicClosure}\ k$ every submodule of $\mathrm{AlgebraicClosure}\ k \otimes_k V$ stable under all the operators $\rho(\sigma)$ is $\bot$ or $\top$. Let $N$ be a nonzero natural number and $S$ a finite set of natural numbers. Then there exist a natural number $\ell$, a valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ and an automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$ such that: $\ell$ is prime, $\ell \notin S$, $\ell \nmid N$, $\ell \equiv 1 \pmod N$, $A$ lies over $\ell$ in the sense that $\ell$ is a nonunit of $A$, $\sigma$ is a Frobenius at $\ell$ for $A$, i.e. $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$, and finally $\mathrm{tr}_k(\rho(\sigma)) \neq \ell + 1$ in $k$.
--
--   This is the implication "absolutely irreducible $\Rightarrow$ non-Eisenstein" for two-dimensional mod $p$ representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with open kernel, in the trace formulation: no congruence $\mathrm{tr}\,\rho(\mathrm{Frob}_\ell) = \ell + 1$ can hold for all primes $\ell \equiv 1 \pmod N$ outside a prescribed finite set. It is used in the cohomological part of the argument, where the traces of Frobenius are the Hecke eigenvalues $\theta(T_\ell)$ of a residual eigensystem of level $N$, to exclude Eisenstein behaviour at suitable auxiliary primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρ : ResidualGaloisRep k) (hρ : ρ.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] (S : Finset ℕ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N ∧ ℓ ≡ 1 [MOD N] ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        LinearMap.trace k ρ.V (ρ.ρ σ) ≠ (ℓ : k) + 1 := by sorry
