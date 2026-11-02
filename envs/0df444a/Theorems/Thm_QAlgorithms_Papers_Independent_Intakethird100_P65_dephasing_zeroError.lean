-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_dephasing_zeroError
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.dephasing_zeroError
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:52:33.429791+00:00
-- url     : https://prove2.me/theorems/0a52db2c-5fee-48fe-8868-ffff152c3694
-- title:
--   Example 4 / Eq.(65): dephasing zero-error cost
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For $0\le p\le1$, let $\mathcal Z_p(X)=(1-p)X+pZXZ$ on a qubit, where $Z=\operatorname{diag}(1,-1)$. Then
--
--   $$S_{\rm NS,0}(\mathcal Z_p)=\tfrac12\log_2(|4p-2|+2).$$
--
--   The formula covers the full probability interval: it is one at either endpoint and one half at $p=1/2$. The separately erroneous printed dual witness is not assumed.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 14, Example 4 / Eq.(65): dephasing zero-error cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Example 4, Eq.(65), PDF p.14: valid for the full probability range;
the erroneous fixed dual witness in Eq.(64) is not assumed. -/
theorem dephasing_zeroError (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    zeroErrorCost (phaseFlipChannel p) = Real.logb 2 (|4*p-2| + 2) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
