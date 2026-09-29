-- Prove2me | Theorems.Thm_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
-- name    : Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7729e2a2-5fa8-5709-a1c4-1e793479a7f1
-- title:
--   Trace is unchanged by a commuting p-power-order factor
-- statement:
--   Let $p$ be a prime, $k$ a field of characteristic $p$, $G$ a group, and $V$ a finite-dimensional $k$-vector space. Given a representation $\rho : G \to \mathrm{GL}(V)$ over $k$ (an element of `Representation k G V`, i.e. a monoid homomorphism from $G$ to the $k$-linear endomorphisms of $V$), elements $g, u \in G$ with $g$ and $u$ commuting, and a natural number $a$ with $u^{p^a} = 1$, the assertion is that the $k$-linear trace of $\rho(gu)$ on $V$ equals the trace of $\rho(g)$: $\operatorname{tr}_{k,V}\rho(g u) = \operatorname{tr}_{k,V}\rho(g)$. No finiteness is imposed on $G$, and $u$ is not required to have exact order $p^a$; only that its order divides $p^a$.
--
--   This is the standard fact underlying the theory of Brauer characters: in characteristic $p$ the trace of $g$ on a finite-dimensional representation depends only on the $p$-regular part of $g$, since the commuting $p$-part acts unipotently. It is used in the proof of [`Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero`](thm.html#Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero), a detection statement of Artin-induction type in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g u : G) (hgu : Commute g u) (a : ℕ) (hu : u ^ p ^ a = 1) :
    LinearMap.trace k V (ρ (g * u)) = LinearMap.trace k V (ρ g) := by sorry
