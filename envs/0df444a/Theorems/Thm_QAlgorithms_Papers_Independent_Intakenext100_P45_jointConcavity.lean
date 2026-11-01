-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_jointConcavity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.jointConcavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:05:51.028335+00:00
-- url     : https://prove2.me/theorems/20a4a86b-0aa5-442c-91db-124ffa24560f
-- title:
--   §4.5, joint concavity of Q and convexity of xi
-- statement:
--   For density pairs $(\rho_0,\sigma_0),(\rho_1,\sigma_1)$ and $t\in[0,1]$, write $\rho_t=t\rho_0+(1-t)\rho_1$ and similarly for $\sigma_t$. Then
--
--   $$Q(\rho_t,\sigma_t)\ge tQ(\rho_0,\sigma_0)+(1-t)Q(\rho_1,\sigma_1),$$
--   $$\xi(\rho_t,\sigma_t)\le t\xi(\rho_0,\sigma_0)+(1-t)\xi(\rho_1,\sigma_1).$$
--
--   The second inequality uses extended nonnegative values, with a zero coefficient contributing zero. These are joint concavity of $Q$ and joint convexity of its negative logarithm.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 18, §4.5, joint concavity of Q and convexity of xi

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.18: §4.5, joint concavity of Q and convexity of xi. Source correction: the cited Lieb premise on PDF p.18 says all real s; it applies here only to 0<=s<=1. The stated conclusion is unchanged; independent moderation required. -/
theorem jointConcavity (r0 r1 s0 s1 : Mat I)
    (hr0 : IsDensityMatrix r0) (hr1 : IsDensityMatrix r1)
    (hs0 : IsDensityMatrix s0) (hs1 : IsDensityMatrix s1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chernoffInfimum ((t : ℂ) • r0 + ((1-t : ℝ) : ℂ) • r1)
      ((t : ℂ) • s0 + ((1-t : ℝ) : ℂ) • s1) ≥
      t*chernoffInfimum r0 s0 + (1-t)*chernoffInfimum r1 s1 ∧
    chernoffDistance ((t : ℂ) • r0 + ((1-t : ℝ) : ℂ) • r1)
      ((t : ℂ) • s0 + ((1-t : ℝ) : ℂ) • s1) ≤
      (t : EReal)*chernoffDistance r0 s0 + ((1-t : ℝ) : EReal)*chernoffDistance r1 s1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
