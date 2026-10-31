-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_affine_hecke_normal_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.affine_hecke_normal_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:47:28.425959+00:00
-- url     : https://prove2.me/theorems/55a01a6d-10fe-4949-ba88-bc3083565a41
-- title:
--   The specified affine Hecke basis
-- statement:
--   Let $S$ be any commutative unital ring, let $q\in S^\times$, and let $n\ge1$. In the affine Hecke algebra $\widehat H_{n,S}(q^2)$ of Definition 6.3, set $x'_j=g_{j-1}\cdots g_1x_1g_1^{-1}\cdots g_{j-1}^{-1}$ for $1\le j\le n$. For a permutation $\alpha\in\mathfrak S_n$, choose a reduced expression $\alpha=s_{i_1}\cdots s_{i_l}$ and let $T_\alpha=g_{i_1}^{-1}\cdots g_{i_l}^{-1}$. For integer labels $a=(a_1,\ldots,a_n)$ at the upper vertices, set
--   $$T'_{\alpha,a}=T_\alpha(x'_n)^{a_n}\cdots(x'_1)^{a_1}.$$
--   The family $(T'_{\alpha,a})_{(\alpha,a)\in\mathfrak S_n\times\mathbb Z^n}$ is an $S$-basis of $\widehat H_{n,S}(q^2)$.
--
--   This is the explicit basis indexed by integer-labelled permutation diagrams; every expansion has finite support. The formalization constructs one reduced word by sorting one-line notation, rather than quantifying an arbitrary lift.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 43, Proposition 6.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Proposition 6.8, PDF pp.43--44: the specified integer-labelled permutation
words form an S-basis, with inverse g generators in T_alpha. -/
theorem affine_hecke_normal_basis (S : Type*) [CommRing S] (q : Sˣ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : Module.Basis (Equiv.Perm (Fin n) × (Fin n → ℤ)) S (NormalizedBraidHecke S q n true),
      ∀ d, b d = heckeNormalWord S q n d := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
