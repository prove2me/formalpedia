-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_lemma_B1_iii
-- name    : TailRiskTheory.Generator.lemma_B1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:31.578203+00:00
-- url     : https://prove2.me/theorems/b6d7e633-0887-41bb-ac42-13fe492104dd
-- title:
--   Lemma B.1 (iii), p. 19 — X ≺st X_p
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. For every $X\in L^\infty$ and every $X_p\in L^\infty$ with the $p$-tail law $\mathbb P(X_p\le x)=(\mathbb P(X\le x)-p)_+/(1-p)$,
--   $$X\prec_{\mathrm{st}}X_p,$$
--   that is, $\mathbb E[f(X)]\le\mathbb E[f(X_p)]$ for every increasing $f:\mathbb R\to\mathbb R$ for which both expectations exist.
--
--   The tail of a risk is stochastically larger than the risk itself; for a monotone generator this gives $\rho(X)\ge\rho^*(X)$.
--
--   **Formalization Note** The space of risks is $L^\infty$; "both expectations exist" is integrability of $f(X)$ and $f(X_p)$.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 19, Lemma B.1 (iii)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Lemma B.1 (iii), p. 19: for `X ∈ 𝒳`, `X ≺st X_p`. -/
theorem lemma_B1_iii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (X Z : Ω → ℝ) (hX : X ∈ Linf P) (hZ : Z ∈ Linf P) (hXZ : IsPTailOf P p X Z) :
    StOrder P X Z := by sorry

end TailRiskTheory.Generator
