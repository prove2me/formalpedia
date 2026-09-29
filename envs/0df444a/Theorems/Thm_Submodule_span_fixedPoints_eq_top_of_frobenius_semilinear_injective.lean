-- Prove2me | Theorems.Thm_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective
-- name    : Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/c16ceebc-7ae1-5535-9cf5-b0466ff8076c
-- title:
--   Fixed vectors of an injective q-semilinear endomorphism span
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ for a prime $p$, and let $V$ be a finite-dimensional $K$-vector space. Let $s$ be a natural number with $s \neq 0$, and put $q = p^{s}$. Let $\theta : V \to V$ be a homomorphism of additive groups which is $q$-semilinear in the sense that $\theta(c \cdot v) = c^{p^{s}} \cdot \theta(v)$ for all $c \in K$ and all $v \in V$, and suppose $\theta$ is injective as a map of sets. Then the $K$-submodule of $V$ spanned by the set of fixed points of $\theta$, namely $\{v \in V : \theta(v) = v\}$, is the whole of $V$. Note that no surjectivity of $\theta$ and no $K$-linearity is assumed: $\theta$ is only additive, with the displayed twisting of scalars by the $q$-power map.
--
--   This is the linear-algebra form of the Lang–Steinberg theorem: an injective $q$-semilinear endomorphism of a finite-dimensional vector space over an algebraically closed field of characteristic $p$ admits a spanning set, hence a basis, of fixed vectors, so that the fixed points constitute an $\mathbb{F}_q$-structure on $V$. It is used in counting the solutions of semilinear equations ([`LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow`](thm.html#LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow)) and, on spaces of differentials on modular curves, to produce enough logarithmic differentials from surjectivity of a Frobenius pushforward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
    {K V : Type*} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v) (hinj : Function.Injective θ) :
    Submodule.span K (Function.fixedPoints θ) = ⊤ := by sorry
