-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_sandwiched_le_petz
-- name    : QAlgorithms.Papers.Independent.Support50.P19.sandwiched_le_petz
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:25:30.244706+00:00
-- url     : https://prove2.me/theorems/535963c3-4954-4118-b4a1-22f612ba7f7e
-- title:
--   Sandwiched divergence is bounded by Petz divergence
-- statement:
--   Let $A,B\ge0$ be arbitrary operators on a positive-dimensional finite complex Hilbert space and let $\alpha>1$. Write $\widetilde D_\alpha$ for the unnormalized sandwiched divergence and $D_\alpha$ for the unnormalized traditional Petz divergence, both in bits and both infinite when $\operatorname{supp}A\not\subseteq\operatorname{supp}B$. Then
--   $$\widetilde D_\alpha(A\Vert B)\le D_\alpha(A\Vert B).$$
--   The logarithmic convention includes $\log_2 0=-\infty$. Neither argument is required to have trace one. This comparison transfers traditional divergence bounds to the sandwiched quantity.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 12, eq13

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

/-- PDF p.12, (13): comparison for all alpha>1 and arbitrary positive operators. -/
theorem sandwiched_le_petz [Nonempty I] (a : ℝ) (ha : 1 < a) (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : sandwichedD a A B ≤ petzD a A B := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
