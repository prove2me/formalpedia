-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_constant_composition_common_code
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.constant_composition_common_code
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:14:49.691171+00:00
-- url     : https://prove2.me/theorems/47ce96af-5ef6-457b-93f7-6b5d2bbad7b0
-- title:
--   Proposition 2: constant-composition common-message cq code
-- statement:
--   Let $W:x\mapsto\rho_x^{BC}$ be a finite cq broadcast channel with nonempty input alphabet and positive-dimensional outputs, and let $p$ be a probability distribution on $X$. Fix $\varepsilon,\delta>0$ and a nonnegative rate
--
--   $$R=\min\{I(X;B),I(X;C)\}-\delta,$$
--
--   where the information quantities are computed in $\bigoplus_xp(x)\rho_x^{BC}$ in bits. For every sufficiently large positive blocklength $n$, there is an indexed family of $\lfloor2^{nR}\rfloor$ words, all of one empirical type $P$ with $\sum_x|P(x)-p(x)|\le\delta$, and separate Bob and Charlie POVMs such that, for every message $m$,
--
--   $$\operatorname{Tr}[(\Lambda_m\otimes\Lambda'_m)\bigotimes_{i=1}^n\rho_{x_i(m)}^{BC}]\ge1-\varepsilon.$$
--
--   The entire code is chosen before the message. This gives constant-composition common-message coding with a joint maximum-error criterion; injectivity of the indexed family is not assumed.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 4, Proposition 2: constant-composition common-message cq code

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

/-- Proposition 2, PDF p.4: constant-composition common-message cq coding.
The code family is chosen before the message and the error is joint maximum error. -/
theorem constant_composition_common_code [Nonempty X] [Nonempty B] [Nonempty C]
    (W : CQChannel X B C) (p : Distribution X) (epsilon delta R : ℝ)
    (he : 0 < epsilon) (hd : 0 < delta) (hR : 0 ≤ R)
    (hRate : R = min (holevoInfo p.val (fun x => traceRight (W.state x)))
      (holevoInfo p.val (fun x => traceLeft (W.state x))) - delta) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ D : CommonCode X B C n (rank n R), D.Good W p epsilon delta := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
