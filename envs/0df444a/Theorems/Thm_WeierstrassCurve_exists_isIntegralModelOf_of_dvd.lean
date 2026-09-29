-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isIntegralModelOf_of_dvd
-- name    : WeierstrassCurve.exists_isIntegralModelOf_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/abfa8029-2601-535e-b0ce-a654c7c794d3
-- title:
--   Integral models of short Weierstrass curves congruent mod n
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$, with coefficients $a_1,a_2,a_3,a_4,a_6$ and associated invariants $c_4(W), c_6(W)$, and let $A$, $B$, $n$ be integers satisfying the two divisibility hypotheses $46656\,n \mid A + 27\,c_4(W)$ and $93312\,n \mid B + 54\,c_6(W)$; that is, $A \equiv -27\,c_4(W)$ modulo $27 \cdot 1728\, n$ and $B \equiv -54\,c_6(W)$ modulo $54 \cdot 1728\, n$. Then there is a Weierstrass equation $W'$ over $\mathbb{Z}$ with the following properties. First, $W'$ is an integral model of the short Weierstrass equation $y^2 = x^3 + Ax + B$ over $\mathbb{Q}$, in the sense that some admissible change of variables $C$ over $\mathbb{Q}$ carries the curve with coefficients $(0,0,0,A,B)$ over $\mathbb{Q}$ to the base change of $W'$ along $\mathbb{Z} \to \mathbb{Q}$. Second, $W'$ has the same first three coefficients as $W$: $a_1(W') = a_1(W)$, $a_2(W') = a_2(W)$, $a_3(W') = a_3(W)$. Third, $a_4(W') \equiv a_4(W)$ and $a_6(W') \equiv a_6(W)$ modulo $n$. Finally, $-27\,c_4(W') = A$ and $-54\,c_6(W') = B$.
--
--   This is the descent step in Kraus's style which converts a congruence condition on the pair $(A,B)$ of a short Weierstrass equation over $\mathbb{Q}$ into an integral model whose coefficients agree with those of a given integral equation $W$ modulo $n$, so that local conditions imposed on $W$ at the primes dividing $n$ transfer coefficientwise to the new equation. It is used in the construction of the auxiliary curve in [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isIntegralModelOf_of_dvd.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_isIntegralModelOf_of_dvd (W : WeierstrassCurve ℤ) (A B n : ℤ) (hA : 46656 * n ∣ A + 27 * W.c₄) (hB : 93312 * n ∣ B + 54 * W.c₆) : ∃ W' : WeierstrassCurve ℤ, W'.IsIntegralModelOf ⟨0, 0, 0, A, B⟩ ∧ W'.a₁ = W.a₁ ∧ W'.a₂ = W.a₂ ∧ W'.a₃ = W.a₃ ∧ W'.a₄ ≡ W.a₄ [ZMOD n] ∧ W'.a₆ ≡ W.a₆ [ZMOD n] ∧ -27 * W'.c₄ = A ∧ -54 * W'.c₆ = B := by sorry
