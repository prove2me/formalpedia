-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_pinching_qq_boundary
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.pinching_qq_boundary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:21:02.478708+00:00
-- url     : https://prove2.me/theorems/bbbb830d-9638-47b8-a03a-c3c139960ada
-- title:
--   Unnumbered result: pinching-channel EPR–GHZ boundary
-- statement:
--   Let $U:A'\to BC$ be any full-environment isometric extension of qutrit rank-$(2,1)$ pinching: Bob's marginal retains the upper-left two-by-two block and the final diagonal entry and deletes all coherences between those blocks. Its closed unassisted EPR–GHZ region, in coordinate order $(Q,Q_B)=(\text{GHZ},\text{Alice–Bob EPR})$, is the nonnegative downward closure of
--
--   $$(Q,Q_B)=(f(p),p),\qquad 0\le p\le1,\qquad f(p)=\begin{cases}1,&p\le\tfrac12,\\H_2(p),&p>\tfrac12.\end{cases}$$
--
--   Here $H_2$ is binary entropy in bits; a block code is tested jointly against the product of GHZ and EPR targets using squared fidelity, with no initial shared resources or side communication. In particular $(1,1/2)$ and $(0,1)$ are allowed. This follows the explicit equation (25) and Theorem 6, recording the paper's incompatible Figure 1 rather than swapping the resources.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 11, Unnumbered result: pinching-channel EPR–GHZ boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Unnumbered specialization after Theorem 6, PDF p.11 and (25) p.8.
Coordinates are (GHZ,EPR_B); follow (25) rather than the erroneous Figure 1. -/
theorem pinching_qq_boundary [Nonempty C]
    (U : Matrix (Fin 3 × C) (Fin 3) ℂ) (hU : Uᴴ * U = 1)
    (hP : ∀ rho, traceRight (conjSuperop U rho) = qutritPinching rho) :
    qqCapacity (conjSuperop U) = pinchingRegion := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
