-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_eb_subadditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P19.eb_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:37:05.798929+00:00
-- url     : https://prove2.me/theorems/fe900521-bfa2-4f7c-b32e-041e5e78b485
-- title:
--   Subadditivity with an entanglement-breaking factor
-- statement:
--   Let $\mathcal N_{\rm EB}:A_1\to B_1$ be an entanglement-breaking channel, let $\mathcal M:A_2\to B_2$ be any channel, and let $1<\alpha\le2$. All spaces are finite-dimensional and nonzero. Then
--   $$\widetilde\chi_\alpha(\mathcal N_{\rm EB}\otimes\mathcal M)\le\widetilde\chi_\alpha(\mathcal N_{\rm EB})+\widetilde\chi_\alpha(\mathcal M).$$
--   The product channel is optimized over arbitrary joint mixed inputs, including entangled inputs. The second channel has no EB restriction. This is the subadditivity relation proved in the paper, without importing later superadditivity results.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 20, theorem18

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

/-- PDF pp.20–21, Theorem 18: EB channel with an arbitrary channel partner; inequality only. -/
theorem eb_subadditivity [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N)
    (M : Superop K L) (hM : IsChannel M) :
    channelInformation true a (tensorChannel N M) ≤
      channelInformation true a N + channelInformation true a M := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
