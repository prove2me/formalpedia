-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_pinching_cq_boundary
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.pinching_cq_boundary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:17:35.11299+00:00
-- url     : https://prove2.me/theorems/8db837c5-670a-4b60-b757-8e2bf7594132
-- title:
--   Unnumbered result (25): pinching-channel CQ boundary
-- statement:
--   Let $\mathcal P$ be qutrit pinching into the span of $|0\rangle,|1\rangle$ and its orthogonal one-dimensional complement: it retains matrix entries $00,01,10,11,22$ and deletes the other off-block entries. Let $U:A'\to BC$ be any rectangular isometry with $\operatorname{Tr}_C\circ\operatorname{Ad}_U=\mathcal P$, so Charlie holds the entire environment. Its unassisted common-classical/Alice–Bob-EPR region is the nonnegative downward closure of
--
--   $$ (R,Q)=(f(p),p),\qquad 0\le p\le1,\qquad f(p)=\begin{cases}1,&p\le\tfrac12,\\H_2(p),&p>\tfrac12,\end{cases}$$
--
--   where $H_2$ is binary entropy in bits. The operational region uses vanishing maximum joint squared-fidelity error and is closed. Equation (25) gives the intended boundary, including $(1,1/2)$, $(0,1)$ and the segment $R=1$, $0\le Q\le1/2$. The incompatible Figure 1 is recorded as a source discrepancy rather than used to swap the resources.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 8, Unnumbered result (25): pinching-channel CQ boundary

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

/-- Equation (25), PDF p.8: ANY full-environment isometric extension of P.
Source correction: follow (25), not the incompatible Figure 1. -/
theorem pinching_cq_boundary [Nonempty C]
    (U : Matrix (Fin 3 × C) (Fin 3) ℂ) (hU : Uᴴ * U = 1)
    (hP : ∀ rho, traceRight (conjSuperop U rho) = qutritPinching rho) :
    cqGenerationCapacity (conjSuperop U) = pinchingRegion := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
