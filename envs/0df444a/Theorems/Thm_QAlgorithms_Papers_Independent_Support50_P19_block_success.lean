-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_block_success
-- name    : QAlgorithms.Papers.Independent.Support50.P19.block_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:36:23.622987+00:00
-- url     : https://prove2.me/theorems/5faed04d-d7e4-40a2-a53d-166759053371
-- title:
--   General finite-block sandwiched success bound
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional channel, $1<\alpha\le2$, and let a uniform $M\ge1$ message unassisted code use $n\ge1$ independent channel uses with actual rate $R=\log_2M/n$ and average success $p_{\rm succ}$. Then
--   $$p_{\rm succ}\le2^{-n\frac{\alpha-1}{\alpha}\left(R-\frac1n\widetilde\chi_\alpha(\mathcal N^{\otimes n})\right)}.$$
--   The encoder may use arbitrary mixed states on all block inputs and the decoder is a joint output POVM. The alpha-Holevo quantity is evaluated on the full block channel. This is the general finite-block bound preceding additivity arguments.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 20, eq17

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

/-- PDF p.20, (17): arbitrary collective block encodings, average uniform-message success. -/
theorem block_success [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (C : UACode (Fin n → I) (Fin n → J) M) :
    ENNReal.ofReal (uaCodeSuccess (channelPower N n) C) ≤
      codingBound n a ((Real.logb 2 (M : ℝ) / (n : ℝ)))
        (((1 / (n : ℝ) : ℝ) : EReal) * channelInformation true a (channelPower N n)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
