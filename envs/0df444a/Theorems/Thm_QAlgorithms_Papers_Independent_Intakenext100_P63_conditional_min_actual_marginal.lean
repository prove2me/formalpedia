-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_conditional_min_actual_marginal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.conditional_min_actual_marginal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:16:50.555179+00:00
-- url     : https://prove2.me/theorems/9327fcf0-23a9-44c6-8981-bae22c9a4582
-- title:
--   Conditional min-entropy dominates the actual-marginal reference bound
-- statement:
--   Let $\rho^{AB}$ be a normalized bipartite density matrix on nonzero finite-dimensional spaces, and put $\rho^B=\operatorname{Tr}_A\rho^{AB}$. Define
--   $H_{\min}(A|B)_\rho=-\log_2\min\{\lambda:\rho^{AB}\le\lambda(I_A\otimes\sigma^B),\ \sigma^B\text{ a normalized density}\}$. With inverse square roots taken on the support and zero eigenvalues mapped to zero,
--
--   $$H_{\min}(A|B)_\rho\ge-\log_2\left\|(I_A\otimes(\rho^B)^{-1/2})\rho^{AB}(I_A\otimes(\rho^B)^{-1/2})\right\|_{\rm op}=:H_\infty(A|B)_\rho.$$
--
--   Here the norm is the Euclidean operator norm. No full-rank assumption is imposed. The inequality compares optimization over all normalized references to the particular actual marginal reference.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 9, Definition 7, supporting comparison with the actual marginal reference

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

/-- PDF p.9, Definition 7: comparison with the actual marginal reference.
The inverse is on its support and the norm is the Euclidean operator norm. -/
theorem conditional_min_actual_marginal {A B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) :
    marginalMinEntropy rho ≤ conditionalMinBits rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
