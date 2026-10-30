-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P42_gaussian_partialStrongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P42.gaussian_partialStrongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:03:46.634602+00:00
-- url     : https://prove2.me/theorems/06209a21-e53d-4a37-b37a-6b2100b2418b
-- title:
--   Gaussian wiretap channel with almost-sure block power
-- statement:
--   Consider the stationary memoryless real Gaussian wiretap channel on Borel alphabets with $Y\mid x\sim N(x,\sigma_1^2)$ and $Z\mid x\sim N(x,\sigma_2^2)$, where $0<\sigma_1<\sigma_2$. A physical realization uses independent Gaussian increments of variances $\sigma_1^2$ and $\sigma_2^2-\sigma_1^2$, with $Z=Y+N_{\mathrm{extra}}$. Fix $S>0$. Arbitrary Borel stochastic encoders must satisfy, at each positive blocklength,
--
--   $$\Pr\!\left\{\sum_{j=1}^n X_j^2\le nS\right\}=1.$$
--
--   Messages are finite, positive and uniform; decoding is deterministic and measurable; errors are average errors. In bits set
--
--   $$C_B=\tfrac12\log_2(1+S/\sigma_1^2),\qquad C_s=C_B-\tfrac12\log_2(1+S/\sigma_2^2),$$
--   $$C_i=\begin{cases}C_B,&i=5,\\C_s,&i=1,2,3,4,6.\end{cases}$$
--
--   For the six literal metrics of Definition 1, vanishing leakage (for every positive threshold, using one code sequence) gives the ordinary and optimistic capacities
--
--   $$C_0^{(i)}=\overline C_1^{(i)}=C_i,$$
--   $$C_\varepsilon^{(i)}=C_i\ (0\le\varepsilon<1),\qquad\overline C_\varepsilon^{(i)}=C_i\ (0<\varepsilon\le1).$$
--
--   Source correction: the printed theorem assigns $C_s$ to all six metrics. Literal $S_5=V/n\le1/n$ removes secrecy, so only its value is changed to Bob's Gaussian channel capacity $C_B$. The almost-sure closed-ball constraint is retained.
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, PDF p. 6, Theorem 5 (Gaussian Wiretap Channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Theorem 5: actual endpoint equality, both endpoint values, and
all epsilon consequences. This is the classical real Gaussian WTC with
0<sigma1<sigma2 and almost-sure block power S>0, not a bosonic channel.
SOURCE CORRECTION (trap 30): printed Theorem 5 assigns CsG to all six metrics.
Changed only S5's value to (1/2)log2(1+S/sigma1^2), preserving its printed formula.
Why: variation/n vanishes for every code, so S5 imposes no secrecy restriction;
Bob's positive-noise, almost-sure-power Gaussian capacity is the remaining value. -/
theorem gaussian_partialStrongConverse
    (sigma1 sigma2 S : ℝ) (hsigma1 : 0 < sigma1)
    (hsigma2 : sigma1 < sigma2) (hS : 0 < S) :
    ∀ i : SecrecyMetric,
      let C : ℝ := if i = .normalizedVariation then
        (1 / 2 : ℝ) * log2 (1 + S / sigma1 ^ 2) else gaussianSecrecyCapacity sigma1 sigma2 S
      gaussianOperationalCapacity sigma1 sigma2 S i false 0 =
        gaussianOperationalCapacity sigma1 sigma2 S i true 1 ∧
      (∀ eps : ℝ, 0 ≤ eps → eps < 1 →
        gaussianOperationalCapacity sigma1 sigma2 S i false eps =
          (C : EReal)) ∧
      (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
        gaussianOperationalCapacity sigma1 sigma2 S i true eps =
          (C : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P42

end
