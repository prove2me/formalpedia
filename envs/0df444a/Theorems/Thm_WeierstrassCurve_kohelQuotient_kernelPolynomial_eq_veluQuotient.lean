-- Prove2me | Theorems.Thm_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient
-- name    : WeierstrassCurve.kohelQuotient_kernelPolynomial_eq_veluQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/7abf6988-62a1-5c9c-b599-9bf6aecfe352
-- title:
--   Kohel's kernel-polynomial quotient equals Vélu's quotient
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$ and associated quantities $b_2,b_4,b_6$, and let $S$ be a finite set of pairs $(x,y)\in R\times R$ such that every $P\in S$ satisfies the affine Weierstrass equation of $W$. Form the kernel polynomial $h=\prod_{P\in S}(X-x_P)\in R[X]$, and let $p_1,p_2,p_3$ denote the first three power sums of the roots of $h$ expressed through its coefficients (`rootPowerSumOne`, `rootPowerSumTwo`, `rootPowerSumThree`). The assertion is that the Weierstrass curve obtained from $W$ by Kohel's recipe applied to $h$, namely the curve with the same $a_1,a_2,a_3$ and with $a_4-5t$, $a_6-b_2t-7w$ for
--   $$t=6p_2+b_2p_1+(\deg h)\,b_4,\qquad w=10p_3+2b_2p_2+3b_4p_1+(\deg h)\,b_6,$$
--   is equal, as a Weierstrass curve over $R$, to Vélu's quotient of $W$ attached to $S$: the curve with the same $a_1,a_2,a_3$ and with $a_4-5\sum_{P\in S}t_P$, $a_6-b_2\sum_{P\in S}t_P-7\sum_{P\in S}w_P$, where $t_P$ and $w_P$ are the per-point quantities `veluT` and `veluW` evaluated at the coordinates of $P$. No subgroup condition on $S$, and no distinctness of the abscissae, is required.
--
--   This identifies Kohel's rewriting of Vélu's isogeny formulas in terms of the kernel polynomial with Vélu's original point-by-point formulas, over an arbitrary commutative ring. It is used in the project wherever a quotient curve must be computed from a polynomial rather than from a list of points, in particular in the statements about deformations and about lifting variable changes for quotients by two- and three-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_kohelQuotient_kernelPolynomial_eq_veluQuotient.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.kohelQuotient_kernelPolynomial_eq_veluQuotient
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))
    (hS : ∀ P ∈ S, W.toAffine.Equation P.1 P.2) :
    W.kohelQuotient (WeierstrassCurve.kernelPolynomial S) = W.veluQuotient S := by sorry
