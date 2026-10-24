-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_strongConverse
-- name    : QAlgorithms.Papers.Independent.Support50.P19.strongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:22:44.191118+00:00
-- url     : https://prove2.me/theorems/21ed5a99-0390-4711-8ffb-989472db8d25
-- title:
--   Exponential strong converse for entanglement-breaking and Hadamard channels
-- statement:
--   Let $\mathcal N:A\to B$ be a channel between positive-dimensional finite complex Hilbert spaces. Suppose that $\mathcal N$ is entanglement breaking or is complementary to an entanglement-breaking channel. Let $C(\mathcal N)$ be its operational unassisted classical capacity. For every real rate $R>C(\mathcal N)$ there exist $c>0$ and an integer $n_0\ge1$ such that every $n\ge n_0$, every positive integer $M$ satisfying $\log_2M/n\ge R$, and every unassisted $M$-message block code obey
--   $$p_{\rm succ}\le 2^{-cn}.$$
--   The messages are uniform, the encoder may use arbitrary mixed states entangled across all $n$ channel inputs, and the decoder is a joint output POVM. The constants precede all block lengths, message numbers, and codes. This makes the operational capacity a sharp communication threshold, including Hadamard channels whose complements lie on the EB boundary.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 1, seed

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

/-- PDF pp.1,21,25–26: exponential strong converse for every EB and every Hadamard channel,
including complements on the EB boundary. Capacity is operational, not defined as Holevo. -/
theorem strongConverse [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N)
    (hclass : IsEB N ∨ IsHadamard N) : UnassistedExponentialConverse N := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
