-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_theorem_1_i
-- name    : TailRiskTheory.Generator.theorem_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:46.896466+00:00
-- url     : https://prove2.me/theorems/ffa5f8a0-6377-48b4-9532-b1e5ce869cee
-- title:
--   Theorem 1 (i), p. 9 — ρ is monotone (translation-invariant, positively homogeneous, comonotonically additive) iff so is ρ∗
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $(\rho,\rho^*)$ be a $p$-tail pair on $L^\infty$: $\rho^*$ is law-invariant and $\rho(X)=\rho^*(X_p)$ for all $X\in L^\infty$. Then each of the following properties holds for $\rho$ if and only if it holds for $\rho^*$:
--
--   1. monotonicity (A1): $\rho(X)\le\rho(Y)$ whenever $X\le Y$ almost surely;
--   2. translation invariance (A2): $\rho(X-m)=\rho(X)-m$ for all $m\in\mathbb R$;
--   3. positive homogeneity (A4): $\rho(\lambda X)=\lambda\rho(X)$ for all $\lambda>0$;
--   4. comonotonic additivity (A6): $\rho(X+Y)=\rho(X)+\rho(Y)$ for comonotonic $X,Y$.
--
--   All properties are over $X,Y\in L^\infty$.
--
--   **Formalization Note** The space of risks is $L^\infty$ (so $\mathcal X^*=\mathcal X$) and risk measures are real-valued. Comonotonicity is the published `Comonotone`: there is $\Omega_0$ of probability one with $(X(\omega)-X(\omega'))(Y(\omega)-Y(\omega'))\ge0$ on $\Omega_0\times\Omega_0$.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 9, Theorem 1 (i)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Theorem 1 (i), p. 9: for a `p`-tail pair `(ρ, ρ^*)`, `ρ` is monotone (translation-invariant,
positively homogeneous, comonotonically additive) if and only if so is `ρ^*`. -/
theorem theorem_1_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar) :
    (IsMonotone P (Linf P) rho ↔ IsMonotone P (Linf P) rhoStar) ∧
    (IsTranslationInvariant (Linf P) rho ↔ IsTranslationInvariant (Linf P) rhoStar) ∧
    (IsPosHomogeneous P rho ↔ IsPosHomogeneous P rhoStar) ∧
    (IsComonoAdditive P rho ↔ IsComonoAdditive P rhoStar) := by sorry

end TailRiskTheory.Generator
