-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_remark4_liminf
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.remark4_liminf
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:32:11.938786+00:00
-- url     : https://prove2.me/theorems/5530e59e-88d2-43cc-bea4-ef497587c0b0
-- title:
--   Signed second-order offset liminf
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. A channel is a completely positive trace-preserving map. Let $0<\varepsilon<1$. Write $L_n=\log_2 M_{\rm ea}^*(\mathcal N^{\otimes n},\varepsilon)$ for the optimal integer-message entanglement-assisted classical coding boundary with uniform messages and average error at most $\varepsilon$. Codes may act collectively and use arbitrary finite pure prior entanglement and local CPTP encoders, followed by a joint receiver POVM. There is no feedback. Let $C_{\rm ea}(\mathcal N)$ be the maximum output-reference quantum mutual information over pure input-reference states, and let $V_{\min}$ and $V_{\max}$ be the minimum and maximum mutual-information variances over all capacity-achieving resource states. All logarithms are base two. Put $V_\varepsilon=V_{\min}$ for $\varepsilon<1/2$ and $V_\varepsilon=V_{\max}$ for $\varepsilon\ge1/2$. The function $\Phi^{-1}$ is the inverse standard normal CDF.
--
--   The signed normalized coding offset satisfies
--
--   $$
--   \liminf_{n\to\infty}\frac{L_n-nC_{\rm ea}(\mathcal N)}{\sqrt n}
--   \ge\sqrt{V_\varepsilon}\,\Phi^{-1}(\varepsilon).
--   $$
--
--   The liminf is taken in the extended real line. At $\varepsilon=1/2$ the right side is zero.
--
--   This is the explicit signed-offset consequence of the achievability theorem, distinct from the subsequently printed dispersion comparison.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 6, Remark 4, (3.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P01

open QAlgorithms Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

-- Reuse pinned accepted definitions; these are not other draft chunks.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

open QAlgorithms.Papers.Independent.Frontier30.P01 (classicalState)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Remark 4, Eq.(3.2): the signed offset liminf, in EReal.
The equality epsilon=1/2 is permitted and gives a zero lower bound. -/
theorem remark4_liminf
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (hN : IsChannel N)
    (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    ((Real.sqrt (epsilonVariance N epsilon) * normalQuantile epsilon : ℝ) : EReal) ≤
      Filter.liminf (fun n : ℕ =>
        (((codingBits (channelPower N n) epsilon - (n : ℝ) * eacSingleLetterCapacity N) /
          Real.sqrt n : ℝ) : EReal)) atTop := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
