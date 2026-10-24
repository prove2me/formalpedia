-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_covariantPair_additivity
-- name    : QAlgorithms.Papers.Independent.Support50.P19.covariantPair_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:44:43.831628+00:00
-- url     : https://prove2.me/theorems/b52f5a20-3b58-49f2-aa20-302dc4cbb6fc
-- title:
--   Pair additivity in the covariant irreducible-output setting
-- statement:
--   Let $1<\alpha\le2$ and let $\mathcal N_i:A_i\to B_i$ be channels on nonzero finite complex spaces. For each channel assume covariance under continuous unitary input and output representations of a compact Hausdorff topological group, with irreducible output representation. Input irreducibility is not required. If
--   $$H_\alpha^{\min}(\mathcal N_1\otimes\mathcal N_2)=H_\alpha^{\min}(\mathcal N_1)+H_\alpha^{\min}(\mathcal N_2),$$
--   then
--   $$\widetilde\chi_\alpha(\mathcal N_1\otimes\mathcal N_2)=\widetilde\chi_\alpha(\mathcal N_1)+\widetilde\chi_\alpha(\mathcal N_2).$$
--   The minimum-output entropies optimize over all mixed density inputs and all logarithms are in bits. The covariance assumptions are the contextual setting of the cited Koenig–Wehner result recovered in this subsection; minimum-output additivity by itself would only give the displayed upper bound for arbitrary channels.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 23, covariantPairAdditivity

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

/-- PDF pp.23–24, 8.1: pair additivity in the inherited covariant irreducible-output
setting of [41]. The bare 'Thus' would not justify this for arbitrary channels. -/
theorem covariantPair_additivity [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (hcovN : CovariantIrreducible N)
    (M : Superop K L) (hM : IsChannel M) (hcovM : CovariantIrreducible M)
    (hadd : minOutput a (tensorChannel N M) = minOutput a N + minOutput a M) :
    channelInformation true a (tensorChannel N M) =
      channelInformation true a N + channelInformation true a M := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
