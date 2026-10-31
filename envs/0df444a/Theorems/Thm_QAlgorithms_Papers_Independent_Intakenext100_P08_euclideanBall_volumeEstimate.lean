-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_euclideanBall_volumeEstimate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.euclideanBall_volumeEstimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:00:00.176335+00:00
-- url     : https://prove2.me/theorems/6cec97cd-6c3b-4747-a1cb-d31a914d1ee1
-- title:
--   Euclidean unit-ball volume bound
-- statement:
--   For a positive integer $n$, let $V_n$ be the Lebesgue volume of the Euclidean unit ball in $\mathbb R^n$. Then
--
--   $$
--   V_n=\frac{\pi^{n/2}}{\Gamma(n/2+1)}\le\left(\frac{2\pi e}{n}\right)^{n/2}.
--   $$
--
--   Here $n/2$ is a real exponent and $\Gamma$ is the gamma function. The volume refers to the ball rather than its boundary surface; this is the estimate used in the geometric decoding bound.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 5, §IV, (48)–(49): Euclidean ball volume estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF p.5, (48)–(49): unit-ball volume identity and upper estimate.
The positive dimension protects division by n, and n/2 is a real exponent. -/
theorem euclideanBall_volumeEstimate (n : ℕ) (hn : 1 ≤ n) :
    unitBallVolume n = Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) ∧
    unitBallVolume n ≤ (2 * Real.pi * Real.exp 1 / (n : ℝ)) ^ ((n : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
