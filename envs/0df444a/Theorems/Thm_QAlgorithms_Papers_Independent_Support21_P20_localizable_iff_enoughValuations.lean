-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_localizable_iff_enoughValuations
-- name    : QAlgorithms.Papers.Independent.Support21.P20.localizable_iff_enoughValuations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:56:20.647972+00:00
-- url     : https://prove2.me/theorems/f52c3935-ff65-442a-a9dd-979fd22a82f8
-- title:
--   Localizability detected by finite continuous valuations
-- statement:
--   Let $A$ be a complete Boolean algebra. It is localizable when $1$ is the supremum of the elements $a$ whose principal Boolean algebra $[0,a]$ admits a faithful finite positive continuous valuation. Then
--
--   $$A\text{ is localizable}\quad\Longleftrightarrow\quad\forall b\ne0\ \exists\nu:A\to[0,\infty):\ \nu\text{ is continuous and }\nu(b)\ne0.$$
--
--   The valuation may depend on $b$; a single faithful global finite valuation is not required. This is the separation criterion used to recognize measurable locales.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 17, Lemma 2.53

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 2.53, PDF p.17: a finite valuation may be chosen after the nonzero open. -/
theorem localizable_iff_enoughValuations (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
