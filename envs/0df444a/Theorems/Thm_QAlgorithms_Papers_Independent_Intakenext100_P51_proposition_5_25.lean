-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_proposition_5_25
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.proposition_5_25
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:07:43.071896+00:00
-- url     : https://prove2.me/theorems/3c6ead71-5580-4f44-8b3e-1ba8c5df31cc
-- title:
--   Unconditional bounded-exponent N4 membership
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge4$. Write $T_{a,b}=T_{a-1}\cdots T_b$ for $a>b$, $T_{a,a}=1$, and $T_{a,b}=T_a\cdots T_{b-1}$ for $a<b$. The representatives in $D_{1,m}$ are $s_{m-1,i}s_{m,j}$ with $1\le i<j\le m$, evaluated by $T_d=T_{m-1,i}T_{m,j}$ as in (5.6).Let $D_2^\circ=\{1,s_{n-2},s_{n-2}s_{n-1}\}$. Define the actual submodule
--   $$N_4=\operatorname{span}_R\{bE_{n-3}X_{n-3}^{\ell}E_{n-1}X_{n-1}^{k}T_{d_1}T_{d_2}:b\in B_{r,n-4}',\ d_1\in D_{1,n-2},\ d_2\in D_2^\circ,\ |\ell|,|k|\le p\}.$$
--   The representative words are evaluated in their displayed order. For all integers $k,\ell$ with $|k|,|\ell|\le p$,
--   $$E_{n-3}X_{n-3}^kE_{n-1}X_{n-1}^{\ell}T_{n-2}T_{n-3}\in N_4.$$
--
--   This conclusion discharges the induction requirement used in the preceding lemmas; that requirement is not assumed here.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 41, Proposition 5.25

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Proposition 5.25, PDF p.41: the unconditional bounded-exponent
membership discharges the induction hypothesis rather than assuming it. -/
theorem proposition_5_25 (p : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 4 ≤ n)
    (k l : ℤ) (hk : |k| ≤ (p : ℤ)) (hl : |l| ≤ (p : ℤ)) :
    ruiXuE P n (n-3) * XPow P n (n-3) k * ruiXuE P n (n-1) * XPow P n (n-1) l *
      T P n (n-2) * T P n (n-3) ∈ nFour P n p := by sorry

end ExplicitSpans

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
