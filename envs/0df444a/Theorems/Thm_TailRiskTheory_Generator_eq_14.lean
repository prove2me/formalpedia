-- Prove2me | Theorems.Thm_TailRiskTheory_Generator_eq_14
-- name    : TailRiskTheory.Generator.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:14.118989+00:00
-- url     : https://prove2.me/theorems/b8bb48f4-fdce-4338-9b3d-c2697a66957e
-- title:
--   Eq. (14), p. 20 — for B ∼ Bern(p) independent of Z and t ⩽ ess-inf(Z), (tB + Z(1 − B))_p =d (ess-inf(Z)B + Z(1 − B))_p =d Z
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. Let $Z\in L^\infty$, let $B\sim\mathrm{Bern}(p)$ (taking values in $\{0,1\}$ with $\mathbb P(B=1)=p$) be independent of $Z$, and let $t\le\operatorname{ess\text{-}inf}(Z)$. Then
--   $$\bigl(tB+Z(1-B)\bigr)_p\overset{d}{=}\bigl(\operatorname{ess\text{-}inf}(Z)B+Z(1-B)\bigr)_p\overset{d}{=}Z, \tag{14}$$
--   that is, the $p$-tail distribution functions $x\mapsto(\mathbb P(V\le x)-p)_+/(1-p)$ of $V=tB+Z(1-B)$ and of $V'=\operatorname{ess\text{-}inf}(Z)B+Z(1-B)$ coincide, and both equal $\mathbb P(Z\le x)$.
--
--   Placing mass $p$ at or below the bottom of the support of $Z$ does not change the $p$-tail. It is the tool by which subadditivity, convexity and $\prec_{\mathrm{cx}}$-monotonicity pass from $\rho$ to its generator.
--
--   **Formalization Note** The space of risks is $L^\infty$. $B$ is the $\mathrm{Bern}(p)$ variable of the sentence that introduces (14).
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), p. 20, Eq. (14) (proof of Theorem 1 (ii))

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)

/-- Eq. (14), p. 20: for `B ∼ Bern(p)`, any `Z ∈ 𝒳^*` independent of `B` and `t ≤ ess-inf(Z)`,
`(tB + Z(1 - B))_p =d (ess-inf(Z)B + Z(1 - B))_p =d Z`. -/
theorem eq_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (Z B : Ω → ℝ) (t : ℝ) (hZ : Z ∈ Linf P) (hB : IsBernoulli P p B) (hind : IndepFun B Z P)
    (ht : t ≤ essInfRV P Z) :
    (∀ x : ℝ, tailDistFn P p (fun ω => t * B ω + Z ω * (1 - B ω)) x =
      tailDistFn P p (fun ω => essInfRV P Z * B ω + Z ω * (1 - B ω)) x) ∧
    IsPTailOf P p (fun ω => essInfRV P Z * B ω + Z ω * (1 - B ω)) Z := by sorry

end TailRiskTheory.Generator
