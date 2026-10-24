-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_eb_power_subadditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P19.eb_power_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:37:47.030257+00:00
-- url     : https://prove2.me/theorems/28622240-88ce-41b0-8324-a8a964713bd4
-- title:
--   Tensor-power subadditivity for EB channels
-- statement:
--   For an entanglement-breaking channel $\mathcal N_{\rm EB}$ on nonzero finite complex spaces, every $1<\alpha\le2$ and every positive integer $n$ satisfy
--   $$\widetilde\chi_\alpha(\mathcal N_{\rm EB}^{\otimes n})\le n\widetilde\chi_\alpha(\mathcal N_{\rm EB}).$$
--   The left side optimizes over all mixed joint input ensembles. The statement gives the tensor-power estimate needed to obtain a single-letter success bound.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 21, corollary19

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

/-- PDF p.21, Corollary 19: full tensor-input quantity for every positive integer n. -/
theorem eb_power_subadditivity [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N) (n : ℕ) (hn : 0 < n) :
    channelInformation true a (channelPower N n) ≤
      ((n : ℝ) : EReal) * channelInformation true a N := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
