-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_corollary_3_17
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.corollary_3_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:01:33.865812+00:00
-- url     : https://prove2.me/theorems/a2152973-a14c-4af8-a263-69fa445878b6
-- title:
--   Finite initial moments and admissibility determine all moments
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed.
--
--   Put $U=\prod_i u_i$ and $\gamma_r(y)=1$ for odd $r$, $-y$ for even $r$. Write $\widetilde w_+(y)=\sum_{a\ge0}\omega_a y^{-a}$ and $\widetilde w_-(y)=\sum_{a\ge1}\omega_{-a}y^{-a}$. All rational expressions below mean their full expansions at infinity, equivalently formal power series in $t=y^{-1}$; they do not require a field of fractions of $R$. Let $F_+(y)$ be the positive rational expression in Lemma 3.16, and let $c_s$ be the coefficient of $z^s$ in $\prod_i(z-u_i)$. Then $u$-admissibility is equivalent to the following three requirements:
--
--   1. The rho choice is $\rho^{-1}\in\{U,-U\}$ for odd $r$, or $\rho^{-1}\in\{q^{-1}U,-qU\}$ for even $r$.
--   2. $\omega_a=[y^{-a}]F_+(y)$ for every $0\le a<r$.
--   3. Both admissibility identities (2.5) hold:
--   $$\sum_{s=0}^r c_s\omega_{s+b}=0\quad(b\in\mathbb Z),\qquad
--   \omega_a=\omega_{-a}+\sum_{i=1}^a\rho^{-1}\delta(\omega_{a-i}\omega_{-i}-\omega_{a-2i})\quad(a\ge1).$$
--
--   The complete integer sequence is controlled by the finite initial positive moments together with these recurrences.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 12, Corollary 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section Moments

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Corollary 3.17, PDF p.12: rho choice, exactly r initial moments, and
full integer-shift admissibility, including the second identity of (2.5). -/
theorem corollary_3_17 (P : Ground R r) :
    RuiXuUAdmissible P ↔ RhoChoice P.toRuiXuUnitParameters ∧
      (∀ a : ℕ, a < r → P.omega (a : ℤ) = PowerSeries.coeff a (positiveRHS P.toRuiXuUnitParameters)) ∧
      RuiXuAdmissible P := by sorry

end Moments

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
