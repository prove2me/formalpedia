-- Prove2me | Theorems.Thm_PadicAlgCl_apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime
-- name    : PadicAlgCl.apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/a15dedea-8172-5a3a-97ee-9fe318f24817
-- title:
--   Inertia fixes roots of unity of order prime to p
-- statement:
--   Let $p$ be a prime and let $\sigma$ be a $\mathbb{Q}_p$-algebra automorphism of `PadicAlgCl p`, an algebraic closure of $\mathbb{Q}_p$ carried with its $p$-adic norm. Assume $\sigma$ moves every element of the closed unit ball by less than $1$: for all $x$ with $\lVert x\rVert \le 1$ one has $\lVert \sigma x - x\rVert < 1$. Let $m$ be a natural number coprime to $p$ (in the sense of `Nat.Coprime p m`, i.e. $\gcd(p,m)=1$), and let $\zeta$ be an element of `PadicAlgCl p` with $\zeta^m = 1$. The conclusion is $\sigma \zeta = \zeta$. Thus the stated metric condition on $\sigma$, which is the defining condition for membership in the inertia group expressed through the norm rather than through a valuation-theoretic structure, forces $\sigma$ to fix every $m$-th root of unity for $m$ prime to $p$. No hypothesis that $\zeta$ be a primitive root of unity, nor that $m$ be positive, is imposed; the case $m = 0$ is excluded automatically, since $\gcd(p,0)=p \ne 1$.
--
--   This is the standard fact that the roots of unity of order prime to $p$ lie in the maximal unramified extension of $\mathbb{Q}_p$, hence are fixed pointwise by inertia, here phrased entirely in terms of the norm on an algebraic closure of $\mathbb{Q}_p$. It is used in the construction of a nonzero vector with prescribed behaviour under a Galois representation whose inertia acts trivially, in [`PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers`](thm.html#PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PadicAlgCl.apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime
    (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1)
    {m : ℕ} (hm : Nat.Coprime p m) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by sorry
