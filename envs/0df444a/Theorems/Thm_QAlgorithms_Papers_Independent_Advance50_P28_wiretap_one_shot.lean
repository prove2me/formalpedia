-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_wiretap_one_shot
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.wiretap_one_shot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:53:29.906998+00:00
-- url     : https://prove2.me/theorems/a463a376-d3ec-44d7-b58d-8e27c969339f
-- title:
--   Theorem 5
-- statement:
--   Let $W^B:X\to\operatorname{Prob}(Y)$ and $W^E:X\to\operatorname{Prob}(Z)$ be classical stochastic channels with countable discrete input and measurable output densities, and let $p$ be an input law. Put $J_t(W,p)=\int(\sum_xp(x)W_x(y)^{1/(1-t)})^{1-t}\,dy=\exp\phi(t\mid W,p)$. Codes have normalized stochastic encoders, disjoint measurable decoding sets, uniform messages, average Bob error $\epsilon_B$, and full $L^1$ message–Eve dependence $d_1$ against their actual Eve marginal. For all positive integers $M,L$, a single code $\Phi$ with $M$ messages satisfies
--   $$\epsilon_B(\Phi)\le3\inf_{0\le t\le1}(ML)^tJ_{-t}(W^B,p),\qquad d_1(\Phi|E)\le9\inf_{0\le t\le1/2}\frac{J_t(W^E,p)}{L^t}.$$
--   The reliability and secrecy parameters can be optimized separately while sharing the existence quantifier. Nonnegative integrals permit infinite channel moments rather than losing countable-input generality.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 13, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.12–13, Theorem 5: ONE code attains both separately optimized
bounds. Countable inputs and measurable density outputs retain the source's generality. -/
theorem wiretap_one_shot {X Y E : Type*} [Countable X] [Nonempty X]
    [MeasurableSpace Y] [MeasurableSpace E]
    (muB : Measure Y) (muE : Measure E)
    (WB : X → Y → ℝ≥0∞) (WE : X → E → ℝ≥0∞)
    (hB : IsDensityChannel muB WB) (hE : IsDensityChannel muE WE)
    (p : X → ℝ≥0∞) (hp : IsENNRealDiscreteLaw p) (M L : ℕ) (hM : 0 < M) (hL : 0 < L) :
    ∃ C : WiretapCode X Y M,
      wiretapDecodingError muB WB C ≤ 3 * sInf ((fun t : ℝ =>
        (M * L : ℝ≥0∞) ^ t * gallagerDensityMoment muB WB p (-t)) '' Set.Icc 0 1) ∧
      codeLeakage muE WE C ≤ 9 * sInf ((fun t : ℝ =>
        gallagerDensityMoment muE WE p t / (L : ℝ≥0∞) ^ t) '' Set.Icc 0 (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
