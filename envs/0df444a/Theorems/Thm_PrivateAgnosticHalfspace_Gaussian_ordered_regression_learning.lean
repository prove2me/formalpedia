-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_regression_learning
-- name    : PrivateAgnosticHalfspace.Gaussian.ordered_regression_learning
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:32.534487+00:00
-- url     : https://prove2.me/theorems/55ce8ed9-238b-4a29-aaa1-40588143028e
-- title:
--   Private Gaussian regression and the complete learning schedule
-- statement:
--   Let $d$ be a natural input dimension, $p$ a natural Hermite cutoff degree, $D_p=\binom{d+p}{p}$ and $T=2\sqrt{D_p}$. There is a probability-valued optimizer realizing the explicit ordered Gaussian regression law. It depends measurably on its deterministic dataset and is replacement differentially private on every dataset for $\varepsilon,\delta\in(0,1/2]$. For every sample size $n>0$, its excess empirical absolute loss is integrable and obeys
--
--   $$\mathbb E[\widehat L_S(V)-\inf_{\|v\|\le1}\widehat L_S(v)]\le120T\sqrt{D_p\log(1/\delta)}/(n\varepsilon).$$
--
--   There are constants $C\ge1$, $0<c\le1/4$ and $C_{\rm dim}>0$, with $2(C+1)^2/c\le C_{\rm dim}$, chosen before all learning parameters and population distributions. For every $\alpha,\beta,\varepsilon,\delta\in(0,1/2]$ and $d\ge C_{\rm dim}\alpha^{-5}$, use the public schedule of Theorem 2.1: degree $p=\lceil C\alpha^{-2}\rceil$, repetition count $k$, threshold count $M$, least admissible training block size $n_0$, validation size $m$ and total $N=kn_0+m$. The schedule exists, has positive $k,M,m$, and satisfies $p\ge1$, $D_p\le n_0$, $p\le D_p$, $M\le p$ and $m\le kn_0$. Its exact sample bound is
--
--   $$N\le k\left[3+\frac{4C^2D_p}{c^2\alpha^2}+\frac{4CD_p\sqrt{\log(1/\delta)}}{c\varepsilon\alpha}\right]+1+C\left(\alpha^{-2}+(\varepsilon\alpha)^{-1}\right)\log(kM/\beta).$$
--
--   For every probability law on real vectors and binary labels whose input marginal is standard Gaussian, Algorithm 1's output law has mass one and
--
--   $$\Pr[\operatorname{err}_P(h)\le\mathrm{OPT}+\alpha]\ge1-\beta.$$
--
--   Here $\mathrm{OPT}$ is the infimum error over all affine halfspaces, without an attainment assumption. The probability includes independent product sampling, all optimizer records and private validation. This is the statistical and privacy component of Theorem 2.1, separated from the operational program theorem.
-- source:
--   Racca, Sanyal and Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, held STOC 2027 submission #1006, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, Algorithm 1, §2.1 equation (4), Appendix B Lemma B.4, and §2.2 arithmetic account. Derived finite Gaussian regression implementation; accelerated recurrence: Ghadimi and Lan, https://arxiv.org/abs/1310.3787v1, p.22 equation (3.36).

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem PrivateAgnosticHalfspace.Gaussian.ordered_regression_learning :
    ∃ O : Optimizer, RealizesOrderedRegression O ∧
      (∀ d p n : ℕ, 0 < n → ∀ ε δ : ℝ,
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        Measurable (fun S => (O d p n ε δ S : Measure (UnitBall d p))) ∧
        PrivateUniformGen.Characterization.IsDP (O d p n ε δ) ε δ ∧
        ∀ S : Fin n → Example d,
          Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val-
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
            (O d p n ε δ S : Measure (UnitBall d p)) ∧
          (∫ v : UnitBall d p, empiricalLoss d p S v.val-
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
            ∂(O d p n ε δ S : Measure (UnitBall d p))) ≤
              120*radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε)) ∧
      ∃ C c Cdim : ℝ, 1 ≤ C ∧ 0 < c ∧ c ≤ 1/4 ∧ 0 < Cdim ∧ 2*(C+1)^2/c ≤ Cdim ∧
      ∀ α β ε δ : ℝ, 0 < α ∧ α ≤ 1/2 → 0 < β ∧ β ≤ 1/2 →
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
      ∀ d : ℕ, Cdim/α^5 ≤ (d : ℝ) →
      let p := scheduledDegree C α
      let D := featureDimension d p
      let k := repetitions β
      let M := thresholds C α
      let n₀ := trainingSize C c α ε δ d p
      let m := validationSize C α β ε k M
      let n := k*n₀+m
      blockCondition C c α ε δ d p n₀ ∧
      (∀ r, blockCondition C c α ε δ d p r → n₀ ≤ r) ∧
      0 < k ∧ 0 < M ∧ 0 < m ∧ 1 ≤ p ∧ D ≤ n₀ ∧ p ≤ D ∧ M ≤ p ∧ m ≤ k*n₀ ∧
      (n : ℝ) ≤ (k : ℝ)*(3+4*C^2*D/(c^2*α^2)+4*C*D*Real.sqrt (Real.log (1/δ))/(c*ε*α))+1+
        C*(α⁻¹^2+(ε*α)⁻¹)*Real.log ((k : ℝ)*M/β) ∧
      ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst=gaussian d →
      let ν := (Measure.pi (fun _ : Fin n => P)).bind (fun S => algorithmLaw O d p k M n₀ m ε δ S)
      IsProbabilityMeasure ν ∧ ν.real {o | error P (decode d p M o) ≤ opt d P+α} ≥ 1-β := by sorry
