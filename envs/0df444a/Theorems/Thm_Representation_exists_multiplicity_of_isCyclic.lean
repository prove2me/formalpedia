-- Prove2me | Theorems.Thm_Representation_exists_multiplicity_of_isCyclic
-- name    : Representation.exists_multiplicity_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/f0eaaf15-1e4d-5ea6-bfc5-5a678f9a9496
-- title:
--   Decomposition of a cyclic-group representation into characters
-- statement:
--   Let $C$ be a finite cyclic abelian group, let $K$ be an algebraically closed field of characteristic $0$, and let $V$ be a finite-dimensional $K$-vector space, together with the routine typeclass assumptions making these notions available. Let $\tau$ be a $K$-linear representation of $C$ on $V$, that is, a monoid homomorphism from $C$ to the $K$-linear endomorphisms of $V$. The assertion is that there exists a finitely supported function $m$ from the group $C \to^{*} K^{\times}$ of characters of $C$ with values in $K^{\times}$ to $\mathbb{N}$ with the following four properties. First, for every $c \in C$ the trace of $\tau(c)$ equals $\sum_{\mu} m(\mu)\,\mu(c)$, the sum being over the support of $m$ and $m(\mu)$ read in $K$ via the natural map. Second, for every $c \in C$ the characteristic polynomial of the endomorphism $\tau(c)$ equals $\prod_{\mu} (X - \mu(c))^{m(\mu)}$ in $K[X]$. Third, the total mass $\sum_{\mu} m(\mu)$ equals $\dim_K V$. Fourth, every character $\mu$ in the support of $m$ satisfies $\mu(c) = 1$ for each $c \in C$ with $\tau(c)$ the identity map on $V$.
--
--   This is the complete reducibility of a representation of a finite cyclic group over an algebraically closed field of characteristic $0$ into one-dimensional characters, recorded not as a direct-sum decomposition but through the multiplicity function $m$ and its trace, characteristic-polynomial and dimension read-outs, with the extra condition that the characters occurring factor through the image of $\tau$. It is used in the analysis of characteristic polynomials of torus elements attached to a cuspidal type, via [`CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq`](thm.html#CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_multiplicity_of_isCyclic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Representation.exists_multiplicity_of_isCyclic {C K V : Type*} [CommGroup C] [Fintype C] [IsCyclic C]
    [Field K] [IsAlgClosed K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K C V) :
    ∃ m : (C →* Kˣ) →₀ ℕ,
      (∀ c, LinearMap.trace K V (τ c) = m.sum fun μ n => (n : K) * ((μ c : Kˣ) : K)) ∧
      (∀ c, (τ c).charpoly = m.prod fun μ n => (X - Polynomial.C ((μ c : Kˣ) : K)) ^ n) ∧
      (m.sum fun _ n => n) = Module.finrank K V ∧
      (∀ μ ∈ m.support, ∀ c, τ c = LinearMap.id → μ c = 1) := by sorry
