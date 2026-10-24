-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_zero_iff
-- name    : QAlgorithms.Papers.Independent.Support50.P19.zero_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:29:53.716368+00:00
-- url     : https://prove2.me/theorems/ecfe4ada-16c7-4ebb-b8ce-bd1ed60757ee
-- title:
--   Equality conditions for the sandwiched divergence
-- statement:
--   Let $\rho,\sigma$ be density operators on a nonzero finite complex Hilbert space and let $1<\alpha\le2$. Then
--   $$\widetilde D_\alpha(\rho\Vert\sigma)=0\quad\Longleftrightarrow\quad\rho=\sigma.$$
--   Equality refers to the complete density operators. This is the faithfulness property of the divergence, beyond equality of a single chosen measurement distribution.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 14, corollary8

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

/-- PDF pp.14–15, Corollary 8: zero divergence iff equality of the entire states. -/
theorem zero_iff [Nonempty I] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) (rho sigma : {X : Matrix I I ℂ // IsDensityMatrix X}) :
    sandwichedD a rho.1 sigma.1 = 0 ↔ rho = sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
