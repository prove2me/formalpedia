-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_theorem_1_iii
-- name    : TailRiskTheory.Generator.theorem_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:44.820411+00:00
-- url     : https://prove2.me/theorems/86480d05-63de-41b0-a6ba-4588c7c86da0
-- title:
--   Theorem 1 (iii), p. 9 — for a p-tail pair (ρ, ρ∗), ρ is coherent (convex, monetary) iff ρ∗ is
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. Let $(\rho,\rho^*)$ be a $p$-tail pair on $L^\infty$: $\rho^*$ is law-invariant and
--   $$\rho(X)=\rho^*(X_p),\qquad X\in L^\infty,$$
--   where $X_p$ is any element of $L^\infty$ with distribution function $\mathbb P(X_p\le x)=(\mathbb P(X\le x)-p)_+/(1-p)$. Then:
--
--   1. $\rho$ is a coherent risk measure if and only if $\rho^*$ is;
--   2. $\rho$ is a convex risk measure if and only if $\rho^*$ is;
--   3. $\rho$ is a monetary risk measure if and only if $\rho^*$ is.
--
--   Here (Definition A.1) a monetary risk measure is monotone, $\rho(X)\le\rho(Y)$ for $X\le Y$ a.s., and translation-invariant, $\rho(X-m)=\rho(X)-m$; a convex risk measure is monetary and convex, $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for $\lambda\in[0,1]$; a coherent risk measure is convex and positively homogeneous, $\rho(\lambda X)=\lambda\rho(X)$ for $\lambda>0$.
--
--   The direction from $\rho^*$ to $\rho$ is the one the paper calls the most important: every coherent (convex) law-invariant risk measure generates a coherent (convex) tail risk measure.
--
--   **Formalization Note** The paper's domain is a convex cone $\mathcal X\supseteq L^\infty$ with $(-\infty,\infty]$-valued risk measures; the statement takes $\mathcal X=L^\infty$, as the paper suggests (p. 5), so $\mathcal X^*=\mathcal X$ and risk measures are real-valued. The relation $\rho(X)=\rho^*(X_p)$ is required for every $Z\in L^\infty$ with the law of $X_p$; no existence of such $Z$ is assumed (atomlessness provides it).
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 9, Theorem 1 (iii) (proof p. 21)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Theorem 1 (iii), p. 9: for a `p`-tail pair `(ρ, ρ^*)`, `ρ` is a coherent (convex, monetary) risk
measure if and only if so is `ρ^*`. -/
theorem theorem_1_iii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar) :
    (IsCoherent P rho ↔ IsCoherent P rhoStar) ∧
    (IsConvexRiskMeasure P rho ↔ IsConvexRiskMeasure P rhoStar) ∧
    (IsMonetary P (Linf P) rho ↔ IsMonetary P (Linf P) rhoStar) := by sorry

end TailRiskTheory.Generator
