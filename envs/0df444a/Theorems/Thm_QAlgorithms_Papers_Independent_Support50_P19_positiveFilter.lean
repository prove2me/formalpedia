-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_positiveFilter
-- name    : QAlgorithms.Papers.Independent.Support50.P19.positiveFilter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:23:41.56818+00:00
-- url     : https://prove2.me/theorems/1619c4aa-94b4-4636-90df-1f675f0680c8
-- title:
--   Positive filtering preserves entanglement breaking
-- statement:
--   Let $\mathcal M:\mathcal B(A)\to\mathcal B(B)$ be a completely positive entanglement-breaking map on positive-dimensional finite complex spaces; trace preservation is not required. For every positive semidefinite operator $Y$ on $B$, define $\mathcal F(X)=Y\mathcal M(X)Y$. Then
--   $$\mathcal F\text{ is completely positive and entanglement breaking}.$$
--   The input and output dimensions may differ, and $Y$ is not normalized. This closure property permits the positive filtering used in the channel subadditivity argument.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 7, remark1

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

/-- PDF p.7, Remark 1: arbitrary rectangular CP EB maps remain CP and EB after filtering. -/
theorem positiveFilter [Nonempty I] [Nonempty J] (N : Superop I J) (hCP : FiniteKrausCP N) (hEB : IsEB N)
    (Y : Matrix J J ℂ) (hY : Y.PosSemidef) :
    FiniteKrausCP (filtered Y N) ∧ IsEB (filtered Y N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
