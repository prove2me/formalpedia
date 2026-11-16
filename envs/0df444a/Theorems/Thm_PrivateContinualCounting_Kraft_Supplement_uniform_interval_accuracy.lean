-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_uniform_interval_accuracy
-- name    : PrivateContinualCounting.Kraft.Supplement.uniform_interval_accuracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:10.326365+00:00
-- url     : https://prove2.me/theorems/cb0bf418-50b9-4db6-b531-b0f200f49bef
-- title:
--   Theorem 1.2 — both directions of uniform interval accuracy
-- statement:
--   Fix $\varepsilon\ge0$, $0<\delta<1$ and $g\in\mathcal G$ with doubling constant $D$. Both following assertions hold.
--
--   1. Every additive data-independent $(\varepsilon,\delta)$-DP counter on any probability space with $N_0=0$ almost surely and finite second moments obeys the necessity implication
--   $$\left[\forall a\ge0,w\ge1:\ \operatorname{Var}(N_{a+w}-N_a)\le C(\ln(w+2))^2g(\ln(w+2))\right]\ \Longrightarrow\ \mathcal K(g).$$
--   No Gaussian, centering, stationary or independent-increment condition is imposed.
--
--   2. If $\mathcal K(g)$ holds, the same real scalar canonical counter as Theorem 1.1(ii), computed from the published spectral weight $f_g$, is admissible and unit-GDP, and for every $w\ge1$,
--   $$\sup_{a\ge0}\operatorname{Var}(N_{a+w}-N_a)\le C'(g,D)(\ln(w+2))^2g(\ln(w+2)).$$
--   The supremum is over a bounded nonempty set, as also asserted. The paper writes $C'$; its Appendix C proof supplies
--   $$C'(g,D)=\Delta^2\max\left\{C_D,\frac{4\int f_g\,dm}{(\ln3)^2}\right\},\qquad\Delta^2=\int f_g^{-1}\,dm.$$
--   This positive constant is independent of start, width and time, and covers widths $1,2$ as well. For every admissible $\mu>0$, this same counter is $\mu$-GDP and $(\varepsilon,\delta)$-DP and all interval and prefix variances are exactly divided by $\mu^2$; the interval envelope is divided by the same factor.
--
--   Together these characterize feasible uniform interval accuracy without imposing time invariance on the input mechanism.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: the paper's C-prime → the explicit positive Appendix C constant for each supplied doubling constant D; reason: this is the constant the source proof establishes, uniformly including widths 1 and 2
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 1, PDF p. 3, Theorem 1.2; proof pp. 9-10, 20-22, PDF pp. 11-12, 22-24

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_GenericOuter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Theorem 1.2(a)–(b). The constant is the one in Appendix C, including w=1,2. -/
theorem uniform_interval_accuracy (ε δ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (g : ℝ → ℝ) (D : ℝ) (hg : IsEnvelopeWith g D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (N : AdditiveNoise Ω P) (C : ℝ), TranscriptDP N.law ε δ →
      (∀ a w : ℕ, 0 < w → N.intervalVariance a w ≤
        C * (Real.log ((w:ℝ)+2))^2 * g (Real.log ((w:ℝ)+2))) → KraftCondition g) ∧
    (KraftCondition g →
      IsLTI (constructedData g) ∧ 0 < intervalConstant g D ∧
      TranscriptGDP (scalarLaw (constructedData g) 1) 1 ∧
      (∀ w : ℕ, 0 < w →
        BddAbove (Set.range (fun a => scalarIntervalVariance (constructedData g) 1 a w)) ∧
        sSup (Set.range (fun a => scalarIntervalVariance (constructedData g) 1 a w)) ≤
          intervalConstant g D * (Real.log ((w:ℝ)+2))^2 * g (Real.log ((w:ℝ)+2))) ∧
      ∀ μ : ℝ, AdmissibleGDP ε δ μ →
        TranscriptGDP (scalarLaw (constructedData g) μ) μ ∧
        TranscriptDP (scalarLaw (constructedData g) μ) ε δ ∧
        (∀ a w : ℕ, 0 < w → scalarIntervalVariance (constructedData g) μ a w =
          scalarIntervalVariance (constructedData g) 1 a w / μ^2 ∧
          scalarIntervalVariance (constructedData g) μ a w ≤
            intervalConstant g D * (Real.log ((w:ℝ)+2))^2 * g (Real.log ((w:ℝ)+2)) / μ^2) ∧
        (∀ t : ℕ, variance (scalarNoise (constructedData g) μ t)
          (gaussianSeed (ℕ × Fin 1)) = (constructedData g).variance t / μ^2)) := by sorry

end PrivateContinualCounting.Kraft.Supplement
