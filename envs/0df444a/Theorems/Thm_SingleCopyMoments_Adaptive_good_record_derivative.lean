-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_good_record_derivative
-- name    : SingleCopyMoments.Adaptive.good_record_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:49.556724+00:00
-- url     : https://prove2.me/theorems/f5f6f87a-d532-4184-8c33-0f4d0d79b66a
-- title:
--   Proposition 41 — Derivative bound on good records
-- statement:
--   Fix $t\ge2$, put $h=\lceil\log_2t\rceil$, $r=2^{h-1}+1$, $\kappa=2(h+1)$ and $K=2(\kappa+2)$. Choose $A=A(K)\ge1$ with the numeric prefactor domination of Lemma 37, set $\zeta=1/[32A(h+1)\log2]$, and choose
--
--   $$0<\alpha\le\min\{1/100,1/(8\kappa),re^{-4/\zeta}/(12K)\}.$$
--
--   There is $C_h>0$ such that for every fixed $0<c_0\le1$, with $T=\lfloor c_0d^{h/(h+1)}\rfloor$, uniformly in interpolation parameter and adaptive single-copy strategy,
--
--   $$\int_{G_\kappa}|\partial_\theta p_\theta|\,d\nu\le C_h\frac{T^{(h+1)/2}}{d^{h/2}}+e(d)\le C_hc_0^{(h+1)/2}+e(d),\qquad e(d)\to0.$$
--
--   The remainder is nonnegative and is chosen before the dimension, parameter, and strategy. It may depend on the fixed $t,A,\alpha,c_0$. The integrand is integrable on good records under the original reference law. This bounds the entire degree sum, with a remainder uniform over dimension-dependent families of protocols.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: a uniform o(1) error and the constants chosen by (7.1) and (7.44) → one vanishing nonnegative remainder before dimension, theta, and strategy, with the explicit numeric parameter predicate; reason: absolute values allow a nonnegative error; its quantifier placement enforces the source uniformity across all adaptive strategies
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Proposition 41, (7.45), printed p. 46 (PDF p. 48); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory Filter
open scoped Topology

namespace SingleCopyMoments.Adaptive

/-- Proposition 41, printed pp.46–48 (PDF pp.48–50). The remainder is chosen
before dimension, interpolation parameter, and strategy; it controls the entire sum. -/
theorem good_record_derivative (t : ℕ) (ht : 2 ≤ t) :
    ∃ C > 0, ∀ A α : ℝ, LowerParameters t α A →
      ∀ c₀ ∈ Set.Ioc (0 : ℝ) 1, ∃ e : ℕ → ℝ,
        (∀ d, 0 ≤ e d) ∧ Tendsto e atTop (nhds 0) ∧
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ hd : 0 < d,
          let T := ⌊c₀ * (d : ℝ)^exponent t⌋₊
          let r : ℕ := 2^(level t-1)+1
          let κ := 2*((level t : ℝ)+1)
          ∀ P : Protocol d, ∀ R : Refinement hd P,
            ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
              IntegrableOn (fun H => |deriv (fun u => densityAt R r α u T H) θ|)
                (goodRecords R T κ) (referenceLaw hd P T) ∧
              derivativeIntegral R r α θ T κ ≤
                C * (T : ℝ)^(((level t : ℝ)+1)/2)/(d : ℝ)^((level t : ℝ)/2) + e d ∧
              C * (T : ℝ)^(((level t : ℝ)+1)/2)/(d : ℝ)^((level t : ℝ)/2) + e d ≤
                C * c₀^(((level t : ℝ)+1)/2) + e d := by sorry

end SingleCopyMoments.Adaptive
