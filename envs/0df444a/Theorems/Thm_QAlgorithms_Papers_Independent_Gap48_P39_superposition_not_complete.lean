-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_superposition_not_complete
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.superposition_not_complete
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:24:52.911206+00:00
-- url     : https://prove2.me/theorems/5241eb94-9906-4ade-9eff-b60e0eca8da7
-- title:
--   §II unnumbered result: superposition need not regularize to capacity
-- statement:
--   Consider the explicit binary cq broadcast channel $x\mapsto|0\rangle\langle0|^B\otimes|x\rangle\langle x|^C$, with a singleton Bob system and noiseless binary Charlie. Let $\mathcal R_{\mathrm{sup}}^\infty(W)=\bigcup_{n\ge1}\frac1n\mathcal R_{\mathrm{sup}}(W^{\otimes n})$ be the raw block-regularized, oriented three-inequality superposition region. Then
--
--   $$\mathcal R_{\mathrm{sup}}^\infty(W)\subsetneq\mathcal C(W),\qquad (0,0,1)\text{ is achievable},$$
--
--   and every triple in the raw superposition union has $R+R_B+R_C=0$. In fact, for every positive blocklength there are deterministic words and separate POVMs sending $\lfloor2^n\rfloor$ Charlie-only messages with zero joint decoding error. The capacities use bits per channel use. This realizes the paper's explicit limitation: superposition in the stated Bob/Charlie orientation need not become complete under regularization.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 4, §II unnumbered result: superposition need not regularize to capacity

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

/-- §II p.4 explicit nonregularization limitation (supporting the seed target).
The oriented superposition union is strictly smaller than capacity: every member
has zero total rate, while Charlie alone receives one bit per use with zero error. -/
theorem superposition_not_complete :
    rawRegularizedSuperposition binaryExample ⊂ cqBroadcastCapacity binaryExample ∧
    (∀ r ∈ rawRegularizedSuperposition binaryExample, r.1 + r.2.1 + r.2.2 = 0) ∧
    cqBroadcastAchievable binaryExample (0, 0, 1) ∧
    (∀ n : ℕ, 0 < n → ∃ D : CQBroadcastCode Bool Unit Bool n 1 1 (rank n 1),
      D.Good binaryExample 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
