-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_erasure_zeroError
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.erasure_zeroError
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:53:13.417085+00:00
-- url     : https://prove2.me/theorems/4c3fb69b-7727-4a21-896a-320295006e92
-- title:
--   Example 5 / Eq.(67): erasure zero-error cost
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let the input dimension be $d\ge1$, let $0\le p\le1$, and let $|e\rangle$ be a new orthogonal erasure flag. Extend $\mathcal E_p$ linearly by $\mathcal E_p(X)=(1-p)X+p\operatorname{Tr}(X)|e\rangle\langle e|$, with the data block embedded in the output. Then
--
--   $$S_{\rm NS,0}(\mathcal E_p)=\tfrac12\log_2(d^2(1-p)+p).$$
--
--   This regularized zero-error cost includes complete erasure and dimension one. The extra dummy index in the printed witness is not used.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 14, Example 5 / Eq.(67): erasure zero-error cost

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

/-- Example 5, Eq.(67), PDF p.14: an orthogonal flag, with the dimension-one
case included. The erroneous extra index in Eq.(66) is not used. -/
theorem erasure_zeroError (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    zeroErrorCost (flaggedErasureChannel A p) =
      Real.logb 2 ((Fintype.card A : ℝ)^2*(1-p) + p) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
