-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_eb_success
-- name    : QAlgorithms.Papers.Independent.Support50.P19.eb_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:38:28.645262+00:00
-- url     : https://prove2.me/theorems/ff587c2c-4188-4659-964e-4bca600fe728
-- title:
--   Single-letter success bound for EB channels
-- statement:
--   Let $\mathcal N_{\rm EB}$ be an entanglement-breaking channel on nonzero finite complex spaces, let $1<\alpha\le2$, and consider any uniform $M\ge1$ message code using $n\ge1$ independent uses. With $R=\log_2M/n$ and average correct decoding probability $p_{\rm succ}$,
--   $$p_{\rm succ}\le2^{-n\frac{\alpha-1}{\alpha}(R-\widetilde\chi_\alpha(\mathcal N_{\rm EB}))}.$$
--   Block codewords may be entangled and the measurement collective. No rate-above-capacity assumption is needed for this finite-block inequality; that assumption is used only to obtain a positive exponent.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 21, eq18

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF p.21, (18): no rate-above-capacity premise is needed for this finite-block bound. -/
theorem eb_success [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (C : UACode (Fin n → I) (Fin n → J) M) :
    ENNReal.ofReal (uaCodeSuccess (channelPower N n) C) ≤
      codingBound n a ((Real.logb 2 (M : ℝ) / (n : ℝ))) (channelInformation true a N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
