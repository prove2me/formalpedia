-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_highOrder_smooth_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.highOrder_smooth_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:16:14.432738+00:00
-- url     : https://prove2.me/theorems/7d173ad8-83ec-4919-9ecf-22f6b986336d
-- title:
--   High-order smooth min-entropy uncertainty for a product measurement
-- statement:
--   Let $M=(M_i)_{i=1}^d$ be a POVM on a nonzero finite-dimensional input space, where $d\ge1$ counts its classical outcomes. Write $\widehat H(M)=\min_\sigma H(\{\operatorname{Tr}\sigma M_i\}_i)$, optimizing over normalized input densities; this minimum is attained. Smooth min-entropy optimizes over normalized states within half trace-norm distance $\varepsilon$. For $0<\varepsilon,\delta<1$, any $n\ge0$, and any normalized, possibly entangled input $\psi$ on $n$ systems,
--
--   $$H_{\min}^{\varepsilon}(M^{\otimes n}(\psi))\ge n(\widehat H(M)-\delta)-\frac{16(\log_2d)^2}{\delta}\log_2\frac1\varepsilon.$$
--
--   Moreover, for fixed $M$ and $\varepsilon$ there is a threshold independent of $\psi$ such that for every subsequent $n$,
--
--   $$H_{\min}^{\varepsilon}(M^{\otimes n}(\psi))\ge n\widehat H(M)-8\log_2d\sqrt{n\log_2(1/\varepsilon)}.$$
--
--   For $d=1$ the smooth output min-entropy is exactly zero for all $n$. The measurement outcome law is represented by its diagonal density. This supplies uncertainty against arbitrary entangled inputs without an independence assumption.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 8, Proposition 6: high-order smooth min-entropy uncertainty

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8,16–17, Proposition 6: both smooth min-entropy uncertainty bounds,
for arbitrary entangled inputs. d is the number of OUTPUT outcomes.
The deterministic d=1 case is included explicitly. -/
theorem highOrder_smooth_uncertainty {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (d : ℕ) (hd : 0 < d) (M : Fin d → Mat E) (hM : IsPOVM M)
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) :
    (∃ psi : Mat E, IsDensityMatrix psi ∧
      shannon (fun i => effectProb (M i) psi) = povmMinimumShannon M) ∧
    (∀ (delta : ℝ), 0 < delta → delta < 1 → ∀ (n : ℕ) (psi : Mat (Fin n → E)),
      IsDensityMatrix psi →
      (n : ℝ) * (povmMinimumShannon M - delta) -
        16 * (Real.logb 2 d) ^ 2 / delta * Real.logb 2 (1 / eps) ≤
        traceSmoothStateMinBits eps (measuredState M n psi)) ∧
    (∃ n0 : ℕ, ∀ n ≥ n0, ∀ psi : Mat (Fin n → E), IsDensityMatrix psi →
      (n : ℝ) * povmMinimumShannon M -
        8 * Real.logb 2 d * Real.sqrt ((n : ℝ) * Real.logb 2 (1 / eps)) ≤
        traceSmoothStateMinBits eps (measuredState M n psi)) ∧
    (d = 1 → ∀ (n : ℕ) (psi : Mat (Fin n → E)), IsDensityMatrix psi →
      traceSmoothStateMinBits eps (measuredState M n psi) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
