-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_degraded_message_outer
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.degraded_message_outer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:24:01.255479+00:00
-- url     : https://prove2.me/theorems/dd879e95-56bf-4216-acc0-a7f9959381b0
-- title:
--   §II-C unnumbered quantum outer bound: degraded message sets
-- statement:
--   Let $W:x\mapsto\rho_x^{BC}$ be any finite cq broadcast channel, with nonempty alphabet and positive-dimensional outputs, and let $(R,R_B,0)$ belong to its closed operational classical capacity region. The third rate is zero: Bob decodes all common information intended for Charlie and his private message. Then a finite quantum auxiliary $T$, a distribution $p(x)$ and normalized states $\rho_x^T$ exist such that, in $\sigma^{TXBC}=\bigoplus_xp(x)\rho_x^T\otimes\rho_x^{BC}$,
--
--   $$R_B\le I(X;B\mid T)_\sigma,\qquad R\le I(T;C)_\sigma,\qquad R+R_B\le I(X;B)_\sigma.$$
--
--   Rates are nonnegative and information quantities are in bits. The operational region uses deterministic encoders, separate receiver POVMs and vanishing maximum joint error. No degraded-channel hypothesis or dimension cap on quantum $T$ is added. This is the authors' quantum outer bound, not the classical-auxiliary exact-capacity theorem cited as background.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 7, §II-C unnumbered quantum outer bound: degraded message sets

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

/-- §II-C quantum outer bound for degraded message sets, PDF p.7.
T is quantum, with no finite dimension cap; the channel need not be degraded. -/
theorem degraded_message_outer [Nonempty X] [Nonempty B] [Nonempty C]
    (W : CQChannel X B C) (R RB : ℝ) (h : (R, RB, 0) ∈ cqBroadcastCapacity W) :
    (R, RB, 0) ∈ quantumOuterRegion W true := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
