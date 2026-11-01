-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_symmetric_private_zero_locking_positive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.symmetric_private_zero_locking_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:20:23.838582+00:00
-- url     : https://prove2.me/theorems/0eb14a61-56aa-42dd-9840-f62900a84e4b
-- title:
--   Zero private capacity and positive weak locking capacity for the symmetric channel
-- statement:
--   For an integer $d\ge1$, let $V:\operatorname{Sym}^2(\mathbb C^d)\hookrightarrow\mathbb C^d\otimes\mathbb C^d$ be the canonical isometric inclusion. Its orthonormal input basis consists of $|ii\rangle$ and $(|ij\rangle+|ji\rangle)/\sqrt2$ for $i<j$. Define $\mathcal S_d$ by tracing out the second output factor; its complement traces out the first. Then
--
--   $$P(\mathcal S_d)=0,\qquad L_W(\mathcal S_d)\ge\tfrac12\log_2d.$$
--
--   These are operational capacities with uniform messages and a uniform independent preshared secret of $o(n)$ bits, vanishing averaged decoding error, and the full trace-norm or full classical $\ell^1$ security criterion. The two marginal channels coincide on the entire symmetric input space. This does not assert independent cloning of arbitrary inputs; the locking advantage uses the allowed sublinear secret.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 12, Theorem 13: symmetric subspace channel has zero private and positive locking capacity

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

/-- PDF p.12, Theorem 13: the entire symmetric subspace channel, not just product inputs.
The normalized inclusion defines equal marginals. A sublinear secret remains allowed. -/
theorem symmetric_private_zero_locking_positive (d : ℕ) (hd : 0 < d) :
    keyedCapacity (dilationMap (universalSymmetricDilation d)) (environment (universalSymmetricDilation d)) false = 0 ∧
    (1 / 2 : ℝ) * Real.logb 2 d ≤
      keyedCapacity (dilationMap (universalSymmetricDilation d)) (environment (universalSymmetricDilation d)) true := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
