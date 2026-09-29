-- Prove2me | Theorems.Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq
-- name    : WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/c2065997-b6c5-58ad-ae1c-d95d444907e2
-- title:
--   Degree of Φₙ - c Ψₙ² is n²
-- statement:
--   Let $R$ be a nontrivial commutative ring, let $W$ be a Weierstrass curve over $R$, let $n$ be an integer and let $c$ be an element of $R$. Working with Mathlib's division polynomials attached to $W$, namely $\Phi_n \in R[X]$ and the polynomial $\Psi_n^2$ (the square of the $n$-th division polynomial, realised as a genuine element of $R[X]$ even for even $n$), the assertion is that the natural-number degree of the difference $\Phi_n - C(c)\,\Psi_n^2$, where $C(c)$ denotes the constant polynomial $c$, equals $|n|^2$, the square of the natural absolute value of $n$. No hypothesis on $n$ or on $c$ is imposed beyond nontriviality of $R$; in particular for $n = 0$ the polynomial is the constant $1$ and the asserted degree is $0$, and for $c = 0$ the statement reduces to the degree of $\Phi_n$ itself.
--
--   Classically this is the statement that, for a point with abscissa $c$, the abscissae of its $n$-division points are the roots of a polynomial of degree exactly $n^2$; it underlies the bound $n^2$ for the degree of multiplication by $n$ on a Weierstrass curve. It is used in the computation of the rank of the field extension cut out by multiplication by $n$ ([`WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le`](thm.html#WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le)) and in the two statements producing, under the hypothesis that all $n$-torsion is trivial, a rational point homomorphism with nonvanishing Wronskian, respectively a Frobenius factorisation of multiplication by $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ) (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 := by sorry
