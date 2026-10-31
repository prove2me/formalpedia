-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_5_15
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_5_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:05:47.378438+00:00
-- url     : https://prove2.me/theorems/f76fb730-038c-470f-8f9b-be261aac89f9
-- title:
--   All lower coefficients lie in the bounded N4,k span
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Write $B_{r,n}$ for the unital algebra with all relations of Definition 2.1; $T_i,E_i,X_j^{\pm1}$ denote its specified generators. Neither $\omega_0\ne0$ nor its invertibility is assumed. Assume $r=2p+1$ with $p\ge0$, and that $\Omega\cup\{\rho\}$ is $u$-admissible in Definition 3.15. A prime on $B_{r,m}'$ denotes its canonical image inside $B_{r,n}$, rather than an assumed embedding. Set $B_{r,0}'=R\cdot1$.
--
--   Let $n\ge4$ and $|k|\le p$. Write $T_{a,b}=T_{a-1}\cdots T_b$ for $a>b$, $T_{a,a}=1$, and $T_{a,b}=T_a\cdots T_{b-1}$ for $a<b$. The representatives in $D_{1,m}$ are $s_{m-1,i}s_{m,j}$ with $1\le i<j\le m$, evaluated by $T_d=T_{m-1,i}T_{m,j}$ as in (5.6). Let $N_{4,k}$ be the span of
--   $$bE_{n-3}X_{n-3}^{\ell_1}E_{n-1}X_{n-1}^{k_1}T_{d_1}T_{d_2},$$
--   where $b\in B_{r,n-4}'$, $d_1\in D_{1,n-2}$, $d_2\in\{1,s_{n-2},s_{n-2}s_{n-1}\}$, $|\ell_1|\le p$, and $|k_1|\le|k|$. Then
--   $$E_{n-3}hE_{n-1}E_{n-2}X_{n-2}^k\in N_{4,k}\qquad(h\in B_{r,n-2}').$$
--
--   This is containment for the complete lower-image coefficient algebra.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 38, Lemma 5.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Lemma 5.15, PDF pp.38--39: containment for all lower-level h, retaining
|k_1|<=|k| and all three d_2 choices. -/
theorem lemma_5_15 (p : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 4 ≤ n)
    (k : ℤ) (hk : |k| ≤ (p : ℤ)) :
    ∀ h ∈ lowerImage P n (n-2),
      ruiXuE P n (n-3) * h * ruiXuE P n (n-1) * ruiXuE P n (n-2) * XPow P n (n-2) k ∈
        nFourBound P n p |k| := by sorry

end ExplicitSpans

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
