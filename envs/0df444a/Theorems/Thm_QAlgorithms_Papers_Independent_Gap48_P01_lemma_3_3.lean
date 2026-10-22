-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_3
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:44:30.294919+00:00
-- url     : https://prove2.me/theorems/9097dfc9-f002-4e87-a338-db1e23967cf1
-- title:
--   Lemma 3.3
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Write $\alpha^p_{ijl}=(Y'_i)^pX_i\cdots X_{j-1}e_j\cdots e_l$, with $1\le i\le j\le l<n$. Empty products equal $1$. The subalgebra $\widetilde B_a^k$ is the canonical image of the algebra on $a$ strands in $B_n^k$, with $\widetilde B_0^k$ the scalar subalgebra; injectivity is not assumed. Angle brackets denote the $R$-linear span.
--
--   For $1\le m\le l$, $p\in\mathbb Z$ and $\gamma\in\{X,e\}$,
--   $$
--   \gamma_m\alpha^p_{ijl}\in\left\langle\alpha^{p'}_{i'j'l}b:
--   1\le i'\le j'\le l,\ b\in\widetilde B_{l-1}^k,\ i'\ge\min(i,m),\ |p'|\le|p|\right\rangle,
--   $$
--   where the generating terms can be restricted to $p'p\ge0$, except when $i'=m$, $m=i$ and $\gamma=X$. Thus the only multiplication that can require negative $p'p$ is $X_i\alpha^p_{ijl}$, and then such terms have $i'=i$.
--
--   This is the chain reduction statement, including its final exceptional-case assertion.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 12, Lemma 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 3.3, PDF pp.12--15. The sign restriction can be dropped only
for X_i acting at m=i, and even then only for a resulting i'=m. -/
theorem lemma_3_3 (l i j m : ℕ) (hl : l < n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjl : j ≤ l) (hm : 1 ≤ m) (hml : m ≤ l)
    (p : ℤ) (g : ℕ → NonsplitBMW P n) (hg : g = (fun t => X P n t false) ∨ g = E P n) :
    g m * alphaChain P n i j l p ∈ alphaSpan P n l
      (fun ip pp => min i m ≤ ip ∧ |pp| ≤ |p| ∧
        (pp*p < 0 → ip = m ∧ m = i ∧ g = (fun t => X P n t false))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
