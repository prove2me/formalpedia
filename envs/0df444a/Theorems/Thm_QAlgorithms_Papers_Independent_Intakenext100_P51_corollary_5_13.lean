-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_corollary_5_13
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.corollary_5_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:05:05.224153+00:00
-- url     : https://prove2.me/theorems/b0dfab67-c5c8-4a90-9a0b-fc5b68962685
-- title:
--   Both lower-image product containments
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge2$, $d\in D_{1,n}$, and $|a|\le p$. Write $T_{a,b}=T_{a-1}\cdots T_b$ for $a>b$, $T_{a,a}=1$, and $T_{a,b}=T_a\cdots T_{b-1}$ for $a<b$. The representatives in $D_{1,m}$ are $s_{m-1,i}s_{m,j}$ with $1\le i<j\le m$, evaluated by $T_d=T_{m-1,i}T_{m,j}$ as in (5.6). Then
--   $$E_{n-1}X_{n-1}^aT_dE_{n-1}\in B_{r,n-2}'E_{n-1},$$
--   and, when $n\ge3$,
--   $$E_{n-1}X_{n-1}^aT_dE_{n-2}\in B_{r,n-2}'E_{n-1}E_{n-2}.$$
--   Here a product with $B'$ denotes the corresponding product submodule.
--
--   The separate lower bound for the second displayed containment ensures that $E_{n-2}$ exists.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 38, Corollary 5.13

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Corollary 5.13, PDF p.38: both containments in the canonical lower-image
product submodules. The E_(n-2) clause requires n>=3. -/
theorem corollary_5_13 (p : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 2 ≤ n)
    (i j : ℕ) (hd : ValidPair n i j) (a : ℤ) (ha : |a| ≤ (p : ℤ)) :
    (3 ≤ n → ruiXuE P n (n-1) * XPow P n (n-1) a * pairWord P n n i j * ruiXuE P n (n-2) ∈
      lowerProduct P n (ruiXuE P n (n-1) * ruiXuE P n (n-2))) ∧
    (ruiXuE P n (n-1) * XPow P n (n-1) a * pairWord P n n i j * ruiXuE P n (n-1) ∈
      lowerProduct P n (ruiXuE P n (n-1))) := by sorry

end ExplicitSpans

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
