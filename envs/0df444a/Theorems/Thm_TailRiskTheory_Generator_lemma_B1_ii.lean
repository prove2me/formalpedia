-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_lemma_B1_ii
-- name    : TailRiskTheory.Generator.lemma_B1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:40.919454+00:00
-- url     : https://prove2.me/theorems/64d7300c-b99a-4eeb-a21e-658df068b29a
-- title:
--   Lemma B.1 (ii), p. 19 — the p-tail and the p-mixture preserve the stochastic order ≺st
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. Write $X\prec_{\mathrm{st}}Y$ if $\mathbb E[f(X)]\le\mathbb E[f(Y)]$ for every increasing $f:\mathbb R\to\mathbb R$ for which both expectations exist. For $X,Y\in L^\infty$:
--
--   1. if $X\prec_{\mathrm{st}}Y$, then $X_p\prec_{\mathrm{st}}Y_p$;
--   2. if $X\prec_{\mathrm{st}}Y$, then $X^{(p)}\prec_{\mathrm{st}}Y^{(p)}$.
--
--   Here $X_p$, $Y_p$ are any elements of $L^\infty$ with the $p$-tail laws $\mathbb P(X_p\le x)=(\mathbb P(X\le x)-p)_+/(1-p)$, and $X^{(p)}$, $Y^{(p)}$ any elements of $L^\infty$ with the mixture laws $\mathbb P(X^{(p)}\le x)=p\,\mathbb 1_{\{x\ge\operatorname{ess\text{-}inf}(X)\}}+(1-p)\mathbb P(X\le x)$.
--
--   Together with law invariance, this is how monotonicity passes between a tail risk measure and its generator.
--
--   **Formalization Note** The space of risks is $L^\infty$; "both expectations exist" is integrability of $f(X)$ and $f(Y)$.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 19, Lemma B.1 (ii)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Lemma B.1 (ii), p. 19: for `X, Y ∈ 𝒳`, if `X ≺st Y` then `X_p ≺st Y_p`; for `X, Y ∈ 𝒳^*`,
if `X ≺st Y` then `X^(p) ≺st Y^(p)`. -/
theorem lemma_B1_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ X ∈ Linf P, ∀ Y ∈ Linf P, ∀ Xt ∈ Linf P, ∀ Yt ∈ Linf P,
      StOrder P X Y → IsPTailOf P p X Xt → IsPTailOf P p Y Yt → StOrder P Xt Yt) ∧
    (∀ X ∈ Linf P, ∀ Y ∈ Linf P, ∀ Xm ∈ Linf P, ∀ Ym ∈ Linf P,
      StOrder P X Y → IsPMixOf P p X Xm → IsPMixOf P p Y Ym → StOrder P Xm Ym) := by sorry

end TailRiskTheory.Generator
