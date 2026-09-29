-- Prove2me | Theorems.Thm_WeierstrassCurve_natDegree_hasseInvariant_jFamily
-- name    : WeierstrassCurve.natDegree_hasseInvariant_jFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8f505577-577c-5f80-b854-1f05b6ae3086
-- title:
--   Hasse polynomial of the j-family: degree and constant term
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $k$ be a field of characteristic $q$. Over the polynomial ring $k[X]$ consider the Weierstrass curve $W$ with coefficients $a_1 = 1$, $a_2 = 0$, $a_3 = 0$, $a_4 = -36X$, $a_6 = -X$, i.e. $y^2 + xy = x^3 - 36X\,x - X$. Its Hasse invariant $\mathtt{hasseInvariant}\ q\ W$ is, by definition, the coefficient of degree $q-1$ of the $((q-1)/2)$-th power of the polynomial attached to the two-torsion cubic of $W$, so it is an element of $k[X]$; concretely it is the coefficient of $Y^{q-1}$ in $(4Y^3 + Y^2 - 144X\,Y - 4X)^{(q-1)/2}$, the exponent being natural-number division. The assertion is the conjunction of two statements about this element of $k[X]$: its `natDegree` equals $(q-1)/4$, again natural-number division, i.e. $\lfloor (q-1)/4 \rfloor$; and its coefficient in degree $0$ equals $1$.
--
--   This computes the degree and constant term of the Hasse (supersingular) polynomial for the one-parameter family $y^2 + xy = x^3 - 36t\,x - t$, whose member with parameter $t$ has $j$-invariant $1/t$ away from degenerate values. It is used by [`WeierstrassCurve.hasseInvariant_jFamily`](thm.html#WeierstrassCurve.hasseInvariant_jFamily) and by [`WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero`](thm.html#WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero) to control the supersingular $j$-invariants in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natDegree_hasseInvariant_jFamily.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.natDegree_hasseInvariant_jFamily
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).natDegree = (q - 1) / 4 ∧
      (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).coeff 0 = 1 := by sorry
