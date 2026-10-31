-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P51_lemma_5_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P51.lemma_5_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:04:20.07612+00:00
-- url     : https://prove2.me/theorems/50b2e6cb-5c24-4032-aa9b-36eea46522bf
-- title:
--   Explicit row-standard permutation representatives and cardinality
-- statement:
--   Let $r\ge1$ and let $R$ be a commutative unital ring. Fix units $q,\delta,\rho,u_1,\ldots,u_r$, with $\delta=q-q^{-1}$, and moments $\omega_a\in R$ for $a\in\mathbb Z$, with $\omega_0=1-\delta^{-1}(\rho-\rho^{-1})$. Let $B_{r,n}$ be the algebra of Definition 2.1 with all its specified relations. No nonzero or invertibility assumption on $\omega_0$ is made. Assume that the parameters are $\mathbf u$-admissible in the sense of Definition 3.15.
--
--   Assume also $r=2p+1$ with $p\ge0$, and let $n\ge1$ and $0\le2f\le n$. Let $D_{f,n}\subseteq\mathfrak S_n$ consist of the permutations for which the standard filling of shape $((n-2f),(2^f))$, acted on the right, has increasing rows and an increasing first column in its second component. For $s_i=(i,i+1)$, write $s_{a,b}=s_{a-1}\cdots s_b$ if $a>b$, $s_{a,a}=1$, and $s_{a,b}=s_a\cdots s_{b-1}$ if $a<b$. Then
--   $$
--   D_{f,n}=\left\{s_{n-2f+1,i_f}s_{n-2f+2,j_f}\cdots s_{n-1,i_1}s_{n,j_1}:\ 1\le i_f<\cdots<i_1\le n,\ 1\le i_k<j_k\le n-2k+2\ (1\le k\le f)\right\},
--   \qquad |D_{f,n}|=\frac{n!}{(n-2f)!f!2^f}.
--   $$
--
--   The equality is between sets of permutations. At $f=0$ the product is empty and $D_{0,n}=\{1\}$. This gives the explicit representatives and count used in the cellular spanning families; the count is stated in the source proof.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, PDF p. 35, Lemma 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

section PermutationTransversal

/-- Lemma 5.5, PDF pp.35--36: equality of the row-standard transversal
and the exact indexed ordered products, together with the cardinality computed
in its proof. Assumption 5.1 is retained; f=0 gives D_(0,n)={1} and count 1. -/
theorem lemma_5_5 {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r)
    (p n f : ℕ) (hr : r = 2*p+1) (hu : RuiXuUAdmissible P) (hn : 0 < n) (hf : 2*f ≤ n) :
    sourceTransversal n f = representativeSet n f ∧
    (sourceTransversal n f).ncard = n.factorial / ((n-2*f).factorial * f.factorial * 2^f) := by sorry

end PermutationTransversal

end QAlgorithms.Papers.Independent.Intakenext100.P51

end
