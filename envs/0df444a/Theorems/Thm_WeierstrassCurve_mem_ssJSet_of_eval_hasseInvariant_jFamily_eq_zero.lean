-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
-- name    : WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8fc8bdbc-8f17-5598-9ab2-aeec72c4b3ba
-- title:
--   Zeros of the Hasse polynomial of the j-family are supersingular
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let $k$ be an algebraically closed field of characteristic $q$. Consider the Weierstrass curve over the polynomial ring $k[X]$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,-36X,-X)$, and let $H \in k[X]$ be its Hasse invariant in the sense of the project, namely the coefficient of $X^{q-1}$ in the $((q-1)/2)$-th power of the cubic polynomial attached to its two-torsion polynomial. Let $t_0 \in k$ satisfy $H(t_0) = 0$ and $1 + 1728 t_0 \ne 0$. The conclusion is twofold: first, $t_0 \ne 0$; second, $1728 + t_0^{-1}$ belongs to `ssJSet q k`, that is, for every Weierstrass curve $W$ over $k$ which is elliptic (discriminant a unit) and satisfies $W.j = 1728 + t_0^{-1}$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is the point at infinity.
--
--   This is the statement that each non-degenerate zero of the Hasse polynomial of the universal family $Y^2 + XY = X^3 - 36tX - t$ produces a supersingular $j$-invariant $1728 + t^{-1}$ in characteristic $q$, supersingularity being expressed as the absence of non-trivial $q$-torsion points on any elliptic Weierstrass curve with that $j$-invariant. It feeds the count of supersingular $j$-invariants obtained from [`WeierstrassCurve.hasseInvariant_jFamily`](thm.html#WeierstrassCurve.hasseInvariant_jFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (t₀ : k) (h : (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval t₀ = 0)
    (hc : 1 + 1728 * t₀ ≠ 0) :
    t₀ ≠ 0 ∧ 1728 + t₀⁻¹ ∈ ssJSet q k := by sorry
