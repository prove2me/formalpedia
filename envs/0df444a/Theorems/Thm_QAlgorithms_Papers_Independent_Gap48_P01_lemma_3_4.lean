-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_4
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:44:59.715269+00:00
-- url     : https://prove2.me/theorems/57268695-2068-4c1e-8a92-27810d212763
-- title:
--   Lemma 3.4
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Write $\alpha^p_{ijl}=(Y'_i)^pX_i\cdots X_{j-1}e_j\cdots e_l$, with $1\le i\le j\le l<n$. Empty products equal $1$. The subalgebra $\widetilde B_a^k$ is the canonical image of the algebra on $a$ strands in $B_n^k$, with $\widetilde B_0^k$ the scalar subalgebra; injectivity is not assumed. Angle brackets denote the $R$-linear span.
--
--   Fix $1\le l<n$ and $0\le K<k$, and put $P_K=\{-K,-K+1,\ldots,k-K-1\}$. Then
--   $$
--   L=\left\langle\alpha^p_{ijl}b:1\le i\le j\le l,\ p\in P_K,\ b\in\widetilde B_{l-1}^k\right\rangle
--   $$
--   is a left ideal of $\widetilde B_{l+1}^k$. This allows every indicated interval containing zero, rather than just the centered interval used later.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 16, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 3.4, PDF p.16. Any interval of k consecutive integers containing
zero is allowed, rather than only the centered interval fixed subsequently.
The standing alpha-chain domain from p.11 requires l>=1. -/
theorem lemma_3_4 (l K : ℕ) (hlpos : 1 ≤ l) (hl : l < n) (hK : K < k) :
    IsLeftIdealIn (level P n (l+1))
      (alphaSpan P n l (fun _ p => -(K:ℤ) ≤ p ∧ p ≤ (k:ℤ)-K-1)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
