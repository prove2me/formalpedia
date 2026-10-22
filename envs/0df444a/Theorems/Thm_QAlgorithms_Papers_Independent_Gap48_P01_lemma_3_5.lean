-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_5
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:45:40.396761+00:00
-- url     : https://prove2.me/theorems/d531636a-9fa0-4e81-8001-0039823025fb
-- title:
--   Lemma 3.5
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Write $\alpha^p_{ijl}=(Y'_i)^pX_i\cdots X_{j-1}e_j\cdots e_l$, with $1\le i\le j\le l<n$. Empty products equal $1$. The subalgebra $\widetilde B_a^k$ is the canonical image of the algebra on $a$ strands in $B_n^k$, with $\widetilde B_0^k$ the scalar subalgebra; injectivity is not assumed. Angle brackets denote the $R$-linear span.
--
--   Put $P=\{-\lfloor(k-1)/2\rfloor,\ldots,\lfloor k/2\rfloor\}$. Suppose $1\le i\le j\le l<n$, $1\le g\le h\le l-2$, $i\le g$ and $p,r\in P$. Then
--   $$
--   \alpha^p_{ijl}\alpha^r_{gh,l-2}\in
--   \left\langle\alpha^{p'}_{i'j'l}\alpha^{r'}_{g'h',l-2}b:
--   1\le i'\le j'\le l,\ 1\le g'\le h'\le l-2,\ i'>i,\ p',r'\in P,\ b\in\widetilde B_{l-3}^k\right\rangle.
--   $$
--   The conclusion increases the first initial index. It imposes no relation $i'>g'$ on the new pair.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 16, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 3.5, PDF pp.16--19. The gain is i'>i; no condition i'>g'
is imposed on the resulting pair of chains. -/
theorem lemma_3_5 (l i j g h : ℕ) (hl : l < n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjl : j ≤ l)
    (hg : 1 ≤ g) (hgh : g ≤ h) (hhl : h ≤ l-2) (hig : i ≤ g)
    (p r : ℤ) (hp : exponentRange k p) (hr : exponentRange k r) :
    alphaChain P n i j l p * alphaChain P n g h (l-2) r ∈ Submodule.span R
      {z | ∃ ip jp gp hh : ℕ, ∃ pp rr : ℤ,
        1 ≤ ip ∧ ip ≤ jp ∧ jp ≤ l ∧ i < ip ∧
        1 ≤ gp ∧ gp ≤ hh ∧ hh ≤ l-2 ∧ exponentRange k pp ∧ exponentRange k rr ∧
        ∃ b ∈ level P n (l-3),
          z = alphaChain P n ip jp l pp * alphaChain P n gp hh (l-2) rr * b} := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
