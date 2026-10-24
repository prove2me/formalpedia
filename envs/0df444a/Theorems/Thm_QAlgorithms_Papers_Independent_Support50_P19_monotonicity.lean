-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_monotonicity
-- name    : QAlgorithms.Papers.Independent.Support50.P19.monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:28:17.253518+00:00
-- url     : https://prove2.me/theorems/ffc1af96-1943-4ed3-a2b3-c8b3d9dc5810
-- title:
--   Data processing for both sandwiched quantities
-- statement:
--   Let $1<\alpha\le2$, let $A,B\ge0$ on a positive-dimensional finite complex input space, and let $\mathcal N$ be a CPTP map to another such space. Then
--   $$\widetilde Q_\alpha(\mathcal N(A)\Vert\mathcal N(B))\le\widetilde Q_\alpha(A\Vert B),\qquad\widetilde D_\alpha(\mathcal N(A)\Vert\mathcal N(B))\le\widetilde D_\alpha(A\Vert B).$$
--   The quasi-relative entropy is unnormalized and extended nonnegative; its base-two logarithmic divergence is extended real. The inputs need not be density operators. This gives monotonicity in precisely the order range proved in the paper.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 14, corollary6

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

/-- PDF p.14, Corollary 6: both monotonicity inequalities, on unnormalized positives. -/
theorem monotonicity [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (N : Superop I J) (hN : IsChannel N) :
    sandwichedTrace a (N A) (N B) ≤ sandwichedTrace a A B ∧
    sandwichedD a (N A) (N B) ≤ sandwichedD a A B := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
