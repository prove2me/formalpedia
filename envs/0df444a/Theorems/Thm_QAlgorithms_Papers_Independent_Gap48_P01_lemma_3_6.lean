-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_6
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:46:10.045593+00:00
-- url     : https://prove2.me/theorems/49bc9a07-6fc0-4d23-840f-b36cbbb2e0a9
-- title:
--   Lemma 3.6
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Write $\alpha^p_{ijl}=(Y'_i)^pX_i\cdots X_{j-1}e_j\cdots e_l$, with $1\le i\le j\le l<n$. Empty products equal $1$. The subalgebra $\widetilde B_a^k$ is the canonical image of the algebra on $a$ strands in $B_n^k$, with $\widetilde B_0^k$ the scalar subalgebra; injectivity is not assumed. Angle brackets denote the $R$-linear span.
--
--   Put $P=\{-\lfloor(k-1)/2\rfloor,\ldots,\lfloor k/2\rfloor\}$. For $0\le l\le n$ and $m\ge0$ with $2m\le l$, let $V^g_{l,m}$ be the set of words $\alpha^{p_1}_{i_1j_1,l-1}\cdots\alpha^{p_m}_{i_mj_m,l-2m+1}$ with $1\le i_f\le j_f\le l-2f+1$ and $p_f\in P$. Let $V_{l,m}$ impose additionally $i_1>\cdots>i_m$. Both sets equal $\{1\}$ at $m=0$ and are empty if $2m>l$. For sets $U,V$, write $UV=\langle uv:u\in U,v\in V\rangle_R$ for their product span.
--
--   For every $l,m$ in these ranges,
--   $$
--   V^g_{l,m}\widetilde B_{l-2m}^k\text{ is a left ideal of }\widetilde B_l^k.
--   $$
--   This includes the zero span when $2m>l$ and the whole level image when $m=0$. It gives left invariance of the general chain construction.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 19, Lemma 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 3.6, PDF p.19. For every m (including 2m>l), the general-chain
product span is a left ideal of the canonical level-l image. -/
theorem lemma_3_6 (l m : ℕ) (hl : l ≤ n) :
    IsLeftIdealIn (level P n l)
      (productSpan (R := R) (chainWords P n l m false) (level P n (l-2*m) : Set (NonsplitBMW P n))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
