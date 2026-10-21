-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_singleLetterConvexity
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.singleLetterConvexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:09:43.344985+00:00
-- url     : https://prove2.me/theorems/7dca79fd-2134-490f-8f56-29af70deb4ce
-- title:
--   Appendix A: convexity of S1
-- statement:
--   Let $\mathcal N:A'\to B$ be a CPTP channel on finite nonzero complex registers. For every normalized finite pure ensemble $\{p_x,\phi_x^{AA'}\}$ on an arbitrary finite reference and the input, put $\sigma_x=(\mathrm{id}\otimes\mathcal N)(\phi_x)$. Zero weights are allowed. In bits let $I(X;B)=H(\sum_xp_x\sigma_x^B)-\sum_xp_xH(\sigma_x^B)$ and $I(A\rangle BX)=\sum_xp_x[H(\sigma_x^B)-H(\sigma_x^{AB})]$. Let $S^{(1)}(\mathcal N)$ be the union of rectangles $0\leq r\leq I(X;B)$, $0\leq R\leq I(A\rangle BX)$ using the same ensemble for both bounds. Then
--
--   $$
--   S^{(1)}(\mathcal N)\text{ is convex}.
--   $$
--
--   In particular, every convex combination with coefficient in the closed interval $[0,1]$ remains in this region. This is the one-letter geometric statement, separate from operational time-sharing; an intermediate flag may enlarge the alphabet.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 12, Appendix A: convexity of S1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Appendix A, PDF p.12 (announced p.4): convexity of the one-letter region,
including lambda=0,1. Flagging may enlarge the alphabet before its reduction. -/
theorem singleLetterConvexity
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    Convex ℝ (cqOneLetterRegion N) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
