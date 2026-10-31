-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_renyi_kl_sharpness_and_limits
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.renyi_kl_sharpness_and_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:55:50.703117+00:00
-- url     : https://prove2.me/theorems/fe5744ac-3d3c-48ab-a040-791fb18d8cb8
-- title:
--   Remarks 52–54: sharp coefficients and binary limiting comparisons
-- statement:
--   The endpoint coefficients $u_\alpha(\beta_1^{-1})$ and $u_\alpha(\beta_2)$ in Theorem 38 are best possible for fixed exact density bounds; equivalently the corresponding KL/Hellinger endpoint comparisons are sharp. For the binary family $P(0)=1/2$, $Q_\varepsilon(0)=1/2-\varepsilon$, the ratio of the complete upper to lower bounds tends to 1 as $\varepsilon\downarrow0$. For the distinct family $P(0)=1/2$, $Q_\varepsilon(0)=\varepsilon$,
--
--   $$\lim_{\varepsilon\downarrow0}\frac{D_\alpha}{\text{lower bound (512)}}
--   =\frac{\alpha}{\log_2(2/(2-\alpha))}\in(1,\ln4)\quad(0<\alpha<1),$$
--
--   while the ratio of $D_\alpha$ to the upper bound (515) tends to 1 for $\alpha>1$. Both binary families and the right-hand limiting direction are retained. The functions are only used eventually for sufficiently small positive epsilon, where all laws and denominators are valid.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 72, Remarks 52–54

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remarks 52–54: sharp coefficients and binary limiting comparisons. Sason--Verdu, arXiv:1508.00335v7, PDF p.72.  -/
theorem renyi_kl_sharpness_and_limits
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    (∀ b1 b2 : ℝ, 0 ≤ b1 → b1 < 1 → 0 ≤ b2 → b2 < 1 →
      (a < 1 → Sharp (kl b) (hellinger a) (exactPairs b1 b2)
        (entropyHellingerKernel b a ((ENNReal.ofReal b1)⁻¹)) ∧
        LowerSharp (kl b) (hellinger a) (exactPairs b1 b2)
          (entropyHellingerKernel b a (ENNReal.ofReal b2))) ∧
      (1 < a → Sharp (kl b) (hellinger a) (exactPairs b1 b2)
        (entropyHellingerKernel b a (ENNReal.ofReal b2)) ∧
        LowerSharp (kl b) (hellinger a) (exactPairs b1 b2)
          (entropyHellingerKernel b a ((ENNReal.ofReal b1)⁻¹)))) ∧
    Tendsto (fun e : ℝ => (renyiUpper b a (binary (1 / 2)) (binary (1 / 2 - e))).toReal /
      (renyiLower b a (binary (1 / 2)) (binary (1 / 2 - e))).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) ∧
    (a < 1 → Tendsto (fun e : ℝ => (renyiDiv b a (binary (1 / 2)) (binary e)).toReal /
      (renyiLower b a (binary (1 / 2)) (binary e)).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (a / (Real.log (2 / (2 - a)) / Real.log 2))) ∧
      1 < a / (Real.log (2 / (2 - a)) / Real.log 2) ∧
      a / (Real.log (2 / (2 - a)) / Real.log 2) < Real.log 4) ∧
    (1 < a → Tendsto (fun e : ℝ => (renyiDiv b a (binary (1 / 2)) (binary e)).toReal /
      (renyiUpper b a (binary (1 / 2)) (binary e)).toReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
