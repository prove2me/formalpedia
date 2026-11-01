-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_twoBasis_capacity_separation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.twoBasis_capacity_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:12:46.615899+00:00
-- url     : https://prove2.me/theorems/1c52c89f-8733-47f1-b027-ae2defcc0169
-- title:
--   An explicit unbounded separation of weak locking and private capacities
-- statement:
--   Let $d\ge1$ be an integer. The input and receiver registers of $\mathcal N_d$ have basis $\{|b,i\rangle:b\in\{0,1\},\ i\in\{0,\ldots,d-1\}\}$, and its environment has dimension $d$. Put $v_{0i}=|i\rangle$ and $v_{1i}=d^{-1/2}\sum_x e^{2\pi\mathrm i ix/d}|x\rangle$. Define the normalized Stinespring isometry $V_d|b,i\rangle=|b,i\rangle\otimes v_{bi}$, with receiver and environment channels obtained by the two partial traces. Then
--
--   $$P(\mathcal N_d)=1,\qquad L_W(\mathcal N_d)=1+\tfrac12\log_2d.$$
--
--   The capacities allow an independent uniform preshared secret of $o(n)$ bits, averaged out in Eve's signal, with averaged decoding error and the full trace-norm or full classical $\ell^1$ security criterion tending to zero. These exact formulas give an unbounded additive separation as $d$ grows. At $d=1$ both capacities are one bit; the actual input and receiver dimension is $2d$.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 1, Abstract, realized by Example 12: unbounded gap between weak locking and private capacities

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

/-- PDF pp.1,11, Example 12, (13)–(14), realizing the abstract's unbounded separation.
At d=1 both capacities equal one bit; input and dilationMap dimension are 2d. -/
theorem twoBasis_capacity_separation (d : ℕ) (hd : 0 < d) :
    keyedCapacity (dilationMap (twoBasisDilation d)) (environment (twoBasisDilation d)) false = 1 ∧
    keyedCapacity (dilationMap (twoBasisDilation d)) (environment (twoBasisDilation d)) true =
      1 + (1 / 2 : ℝ) * Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
