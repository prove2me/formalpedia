-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_theorem_1_ii
-- name    : TailRiskTheory.Generator.theorem_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:00.030495+00:00
-- url     : https://prove2.me/theorems/73f3bcba-87c4-42b9-98a1-1ad9cbcbd73d
-- title:
--   Theorem 1 (ii), p. 9 — if ρ is subadditive (convex, ≺cx-monotone) then so is ρ∗
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $(\rho,\rho^*)$ be a $p$-tail pair on $L^\infty$. Then, over $X,Y\in L^\infty$:
--
--   1. if $\rho$ is subadditive, $\rho(X+Y)\le\rho(X)+\rho(Y)$, then so is $\rho^*$;
--   2. if $\rho$ is convex, $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for $\lambda\in[0,1]$, then so is $\rho^*$;
--   3. if $\rho$ is $\prec_{\mathrm{cx}}$-monotone, $\rho(X)\le\rho(Y)$ whenever $X\prec_{\mathrm{cx}}Y$, then so is $\rho^*$.
--
--   The converses fail in general: the tail standard deviation of Example 1 (p. 8) has a subadditive, convex and $\prec_{\mathrm{cx}}$-monotone generator but is none of these.
--
--   **Formalization Note** The space of risks is $L^\infty$. $X\prec_{\mathrm{cx}}Y$ means $X,Y$ integrable and $\mathbb E[f(X)]\le\mathbb E[f(Y)]$ for every convex $f$ for which both expectations exist.
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 9, Theorem 1 (ii)

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Theorem 1 (ii), p. 9: for a `p`-tail pair `(ρ, ρ^*)`, if `ρ` is subadditive (convex,
`≺cx`-monotone) then so is `ρ^*`. -/
theorem theorem_1_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar) :
    (IsSubadditive P rho → IsSubadditive P rhoStar) ∧
    (IsConvexRM P rho → IsConvexRM P rhoStar) ∧
    (IsCxMonotone P rho → IsCxMonotone P rhoStar) := by sorry

end TailRiskTheory.Generator
