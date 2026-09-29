-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
-- name    : WeierstrassCurve.eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6b464bf0-eb43-5299-85d8-61689f7dc352
-- title:
--   Supersingular j-invariants are zeros of the j-family Hasse invariant
-- statement:
--   Let $q$ be a prime with $5 \le q$ and let $k$ be an algebraically closed field of characteristic $q$. Let $a \in k$ satisfy two conditions: first, $a$ lies in `ssJSet q k`, that is, for every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $W.j = a$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is the point at infinity; second, $a \neq 1728$. Consider the Weierstrass curve over the polynomial ring $k[t]$ given by the coefficient tuple $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,-36t,-t)$, i.e. $y^2 + xy = x^3 - 36tx - t$, and form its Hasse invariant in the sense of [`WeierstrassCurve.hasseInvariant`](def/WeierstrassCurve_HasseInvariant.html#L11): the coefficient of degree $q-1$ of the $((q-1)/2)$-th power of the cubic $4x^3 + b_2x^2 + 2b_4x + b_6$ attached to the curve, an element of $k[t]$. The assertion is that this polynomial in $t$, evaluated at $(a - 1728)^{-1} \in k$, is zero.
--
--   This is one direction of Deuring's criterion in the coordinate $t = (j-1728)^{-1}$ on the $j$-line: a supersingular $j$-invariant $a \neq 1728$ gives a root of the Hasse invariant of the universal one-parameter family with $j = 1728 + t^{-1}$. It is the pointwise input to [`WeierstrassCurve.hasseInvariant_jFamily`](thm.html#WeierstrassCurve.hasseInvariant_jFamily), which identifies the supersingular locus with the zero set of that polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h1728 : a ≠ 1728) :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval (a - 1728)⁻¹ = 0 := by sorry
