-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_proposition_5_27
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.proposition_5_27
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:08:07.614978+00:00
-- url     : https://prove2.me/theorems/269dd3ee-761b-4ef8-8e68-720114ea0d5b
-- title:
--   The specified N2 span is a right module
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge4$. The representatives of $D_{2,n}$ are the permutations
--   $$s_{n-3,i_2}s_{n-2,j_2}s_{n-1,i_1}s_{n,j_1},\qquad 1\le i_2<i_1,\quad i_2<j_2\le n-2,\quad i_1<j_1\le n,$$
--   with $T_d$ evaluated in that displayed order. Define
--   $$N_2=\operatorname{span}_R\{bE_{n-3}X_{n-3}^kE_{n-1}X_{n-1}^{\ell}T_d:b\in B_{r,n-4}',\ |k|,|\ell|\le p,\ d\in D_{2,n}\}.$$
--   Then
--   $$N_2B_{r,n}\subseteq N_2.$$
--
--   Both exponents and the canonical lower-image coefficient algebra are part of the specified span.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 41, Proposition 5.27

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Proposition 5.27, PDF pp.41--43: right stability of the actual N_2
span with canonical B'_(n-4) coefficients and D_(2,n) representative words. -/
theorem proposition_5_27 (p : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 4 ≤ n) :
    ∀ z ∈ nTwo P n p, ∀ a : RuiXuBMW P n, z * a ∈ nTwo P n p := by sorry

end ExplicitSpans

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
