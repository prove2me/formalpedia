-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_3_16
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_3_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:00:57.54974+00:00
-- url     : https://prove2.me/theorems/4b571df6-20aa-40f1-95a8-926cee61bfec
-- title:
--   u-admissibility is equivalent to both generating-series identities
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   Put $U=\prod_i u_i$ and $\gamma_r(y)=1$ for odd $r$, $-y$ for even $r$. Write $\widetilde w_+(y)=\sum_{a\ge0}\omega_a y^{-a}$ and $\widetilde w_-(y)=\sum_{a\ge1}\omega_{-a}y^{-a}$. All rational expressions below mean their full expansions at infinity, equivalently formal power series in $t=y^{-1}$; they do not require a field of fractions of $R$. Then $\Omega\cup\{\rho\}$ is $u$-admissible if and only if $\rho^{-1}\in\{U,-U\}$ for odd $r$ or $\rho^{-1}\in\{q^{-1}U,-qU\}$ for even $r$, and both identities hold:
--   $$\widetilde w_+(y)=\frac{y^2}{y^2-1}-\delta^{-1}\rho+\left(\delta^{-1}\rho U+\frac{y\gamma_r(y)}{y^2-1}\right)U\prod_i\frac{y-u_i^{-1}}{y-u_i},$$
--   $$\widetilde w_-(y)=\frac1{y^2-1}+\delta^{-1}\rho-\frac1U\left(\delta^{-1}\rho U-\frac{y}{\gamma_r(y)(y^2-1)}\right)\prod_i\frac{y-u_i}{y-u_i^{-1}}.$$
--
--   This characterizes all the moments over an arbitrary commutative coefficient ring, including the zero ring.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 11, Lemma 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section Moments

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Lemma 3.16, PDF pp.11--12: equivalence with BOTH complete series at infinity,
not finite truncations or analytic limits. The ring may be the zero ring. -/
theorem lemma_3_16 (P : Ground R r) :
    RuiXuUAdmissible P ↔ RhoChoice P.toRuiXuUnitParameters ∧
      positiveSeries P = positiveRHS P.toRuiXuUnitParameters ∧ negativeSeries P = negativeRHS P.toRuiXuUnitParameters := by sorry

end Moments

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
