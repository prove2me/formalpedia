-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_5_11
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_5_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:04:43.660203+00:00
-- url     : https://prove2.me/theorems/8805bed5-dffd-4664-a91e-a064d656d5c6
-- title:
--   The specified N1 span is a right module
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge2$. Write $T_{a,b}=T_{a-1}\cdots T_b$ for $a>b$, $T_{a,a}=1$, and $T_{a,b}=T_a\cdots T_{b-1}$ for $a<b$. The representatives in $D_{1,m}$ are $s_{m-1,i}s_{m,j}$ with $1\le i<j\le m$, evaluated by $T_d=T_{m-1,i}T_{m,j}$ as in (5.6). Define
--   $$N_1=\operatorname{span}_R\{bE_{n-1}X_{n-1}^aT_d:b\in B_{r,n-2}',\ d\in D_{1,n},\ |a|\le p\}.$$
--   Then
--   $$N_1B_{r,n}\subseteq N_1.$$
--
--   Thus this actual submodule is stable under every right multiplier, also at $n=2$ with the scalar lower image.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 36, Lemma 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Lemma 5.11, PDF pp.36--38: the specified span is stable under every
right multiplier, including n=2 with the scalar lower image. -/
theorem lemma_5_11 (p : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 2 ≤ n) :
    ∀ z ∈ nOne P n p, ∀ a : RuiXuBMW P n, z * a ∈ nOne P n p := by sorry

end ExplicitSpans

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
