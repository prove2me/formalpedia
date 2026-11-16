-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_exact_interval_identity
-- name    : PrivateContinualCounting.Kraft.Supplement.exact_interval_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:59.581897+00:00
-- url     : https://prove2.me/theorems/0473533d-527c-4ceb-bc73-01bfd859743d
-- title:
--   Lemma 3.3 — complete interval identity and generic outer interface
-- statement:
--   For the canonical real scalar counter associated to any $g\in\mathcal G$ satisfying $\mathcal K(g)$, let $h$ be its outer factor, $f=f_g$ its spectral density, $\Delta^2=\|1/h\|_2^2$, and $p_w(z)=\sum_{j<w}z^j$. For every $w\ge1$ and $a\ge0$,
--   $$\operatorname{Var}(N_{a+w}-N_a)=\Delta^2\sum_{m=0}^{a+w-1}|[z^m](p_wh)|^2.$$
--   The variance is nondecreasing in $a$, converges to $\Delta^2\|p_wh\|_2^2$, and
--   $$\sup_{a\ge0}\operatorname{Var}(N_{a+w}-N_a)=\Delta^2\|p_wh\|_2^2=\Delta^2\int F_w f\,dm.$$
--   Every clause is also asserted for any admissible real scalar LTI factors with $h\in H^2$ and $l_n=\sum_{j\le n}h_j$, using $f=|h^*|^2$. This is the generic identity explicitly identified after Lemma 3.4.
--
--   The Appendix C outer interface used by Corollary 1.3 is included: for every even positive-almost-everywhere measurable density $f$ with $f,\log f,f^{-1}$ integrable, the explicitly computed $h_f$ is analytic and zero-free in the disc; $h_f,1/h_f$ are outer, have real Taylor coefficients and the stated power-series expansions; the decoder coefficients are cumulative sums of those of $h_f$; their boundary moduli squared are $f,f^{-1}$; and $\|h_f\|_2^2=\int f\,dm$, $\Delta^2=\int f^{-1}\,dm$. Its real scalar factors are admissible and obey the full interval identity above. These are conclusions, including all norm and exact-convolution obligations.
--
--   The identity connects a single infinite Gaussian release process to arbitrary spectral densities, rather than only a finite truncation or one chosen interval.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: Lemma 3.3 and the generic outer construction in Appendix C → one statement also supplies the source-explicit generic identity and its outer interface; reason: Corollary 1.3 uses an arbitrary density; no additional numbered source result is invented
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, Lemma 3.3

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_GenericOuter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 3.3, with the source-explicit generic H² identity and Appendix C outer
interface needed for the arbitrary density in Corollary 1.3. -/
theorem exact_interval_identity :
    (∀ (g : ℝ → ℝ), IsEnvelope g → KraftCondition g →
      IntervalIdentity (constructedData g) (outerCoeff g) (spectralWeight g)) ∧
    (∀ (d : LTIData ℝ 1) (h : ℕ → ℂ), IsLTI d → h ∈ InfoShareH2.H2 →
      (∀ n, (d.l n 0 : ℂ) = ∑ j ∈ Finset.range (n+1), h j) →
      IntervalIdentity d h (fun θ => ‖positiveBoundary h θ‖^2)) ∧
    (∀ (f : ℝ → ℝ), IsOuterDensity f →
      AnalyticOnNhd ℂ (densityOuter f) (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → densityOuter f z ≠ 0) ∧
      InfoShareH2.IsOuter (taylorAtZero (densityOuter f)) ∧
      InfoShareH2.IsOuter (taylorAtZero (fun z => 1 / densityOuter f z)) ∧
      (∀ n : ℕ, (taylorAtZero (densityOuter f) n).im = 0 ∧
        (taylorAtZero (fun z => 1 / densityOuter f z) n).im = 0 ∧
        (taylorAtZero (fun z => densityOuter f z / (1-z)) n).im = 0) ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        HasSum (fun n => taylorAtZero (densityOuter f) n * z^n) (densityOuter f z) ∧
        HasSum (fun n => taylorAtZero (fun z => 1 / densityOuter f z) n * z^n)
          (1 / densityOuter f z) ∧
        HasSum (fun n => taylorAtZero (fun z => densityOuter f z / (1-z)) n * z^n)
          (densityOuter f z / (1-z))) ∧
      (∀ n, taylorAtZero (fun z => densityOuter f z / (1-z)) n =
        ∑ j ∈ Finset.range (n+1), taylorAtZero (densityOuter f) j) ∧
      (∀ᵐ θ ∂circleMeasure, ‖positiveBoundary (taylorAtZero (densityOuter f)) θ‖^2 = f θ) ∧
      (∀ᵐ θ ∂circleMeasure,
        ‖positiveBoundary (taylorAtZero (fun z => 1 / densityOuter f z)) θ‖^2 = 1 / f θ) ∧
      hardyNormSq (taylorAtZero (densityOuter f)) = (∫ θ, f θ ∂circleMeasure) ∧
      IsLTI (densityData f) ∧
      (densityData f).deltaSq = (∫ θ, 1 / f θ ∂circleMeasure) ∧
      IntervalIdentity (densityData f) (taylorAtZero (densityOuter f)) f) := by sorry

end PrivateContinualCounting.Kraft.Supplement
