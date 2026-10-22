-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_cq_superposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.cq_superposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:13:18.973996+00:00
-- url     : https://prove2.me/theorems/5ce68ea7-5715-4780-8c29-6407f8327523
-- title:
--   Theorem 1 and its explicit nonregularization limitation (seed paper result)
-- statement:
--   Let $W:x\mapsto\rho_x^{BC}$ be a finite-dimensional classical-input quantum broadcast channel with nonempty input alphabet $X$ and positive-dimensional outputs $B,C$. Let $\mathcal C(W)$ be the closure of its operational classical rate region: deterministic input words, independent common/Bob/Charlie messages, separate receiver POVMs, and vanishing maximum joint decoding error. Message counts at blocklength $n$ are $\lfloor2^{nR}\rfloor$, and similarly for the private rates. If a nonnegative rate triple and a probability distribution $p(t,x)$ satisfy
--
--   $$R_B\le I(X;B\mid T),\qquad R+R_C\le I(T;C),\qquad R+R_B+R_C\le I(X;B),$$
--
--   then $(R,R_B,R_C)\in\mathcal C(W)$. All information quantities are evaluated in $\sigma^{TXBC}=\bigoplus_{t,x}p(t,x)\rho_x^{BC}$, with base-two entropy. It suffices to use $|T|\le\min\{|X|,|B|^2+|C|^2-1\}$. This is the superposition inner bound, with boundary rates interpreted in the closed operational region.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 4, Theorem 1 and its explicit nonregularization limitation (seed paper result)

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

/-- Theorem 1, PDF p.4, proved pp.5–6: all three inequalities imply membership
in CLOSED capacity, the limiting boundary interpretation after expurgation. -/
theorem cq_superposition [Nonempty X] [Nonempty B] [Nonempty C] (W : CQChannel X B C) :
    superpositionRegion W (some (superpositionCap X B C)) ⊆ cqBroadcastCapacity W := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
