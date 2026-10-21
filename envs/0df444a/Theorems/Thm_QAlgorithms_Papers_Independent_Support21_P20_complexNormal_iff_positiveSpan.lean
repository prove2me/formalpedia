-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_complexNormal_iff_positiveSpan
-- name    : QAlgorithms.Papers.Independent.Support21.P20.complexNormal_iff_positiveSpan
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:57:59.586759+00:00
-- url     : https://prove2.me/theorems/cc7dd6da-d101-406a-a538-969606d98a18
-- title:
--   Complex normal valuations are spanned by positive normal valuations
-- statement:
--   Let $L$ be any locale and let $\nu:L\to\mathbb C$ be a function. Let $\mathcal P(L)$ denote the finite-valued positive normal valuations, embedded in complex-valued functions by the usual inclusion $[0,\infty)\subset\mathbb C$. Then
--
--   $$\nu\text{ is a complex normal valuation}\quad\Longleftrightarrow\quad\nu\in\operatorname{span}_{\mathbb C}\mathcal P(L).$$
--
--   Normality means continuity on nonempty directed suprema and $\nu(\neg\neg a)=\nu(a)$ for every open $a$. No Stonean hypothesis is imposed. The assertion describes the full linear span, including the zero function.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 19, Corollary 2.60

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Corollary 2.60, PDF p.19: general locales, with no Stonean restriction. -/
theorem complexNormal_iff_positiveSpan (L : Type u) [Order.Frame L] (nu : L → ℂ) :
    IsNormalValuation nu ↔ nu ∈ Submodule.span ℂ
      {f : L → ℂ | ∃ mu : L → ℝ≥0, IsPositiveNormalValuation mu ∧
        f = fun a => ((mu a : ℝ) : ℂ)} := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
