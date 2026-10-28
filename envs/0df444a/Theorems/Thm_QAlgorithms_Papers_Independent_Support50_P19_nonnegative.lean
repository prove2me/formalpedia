-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_nonnegative
-- name    : QAlgorithms.Papers.Independent.Support50.P19.nonnegative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:29:07.727059+00:00
-- url     : https://prove2.me/theorems/a0dcd064-ae98-48c5-a941-fddf3ee8bbb0
-- title:
--   Positivity of the sandwiched divergence
-- statement:
--   For density operators $\rho,\sigma$ on a nonzero finite complex space and $1<\alpha\le2$,
--   $$\widetilde D_\alpha(\rho\Vert\sigma)\ge0.$$
--   Both operators are positive semidefinite with trace one, and unsupported pairs have divergence $+\infty$. Normalization is essential to this positivity statement, which establishes the divergence as a measure of distinguishability.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 14, corollary7

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

/-- PDF p.14, Corollary 7: nonnegativity for normalized states, only the proved order range. -/
theorem nonnegative [Nonempty I] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) (rho sigma : {X : Matrix I I ℂ // IsDensityMatrix X}) :
    0 ≤ sandwichedD a rho.1 sigma.1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
