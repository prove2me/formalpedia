-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_jointQuasiConvexity
-- name    : QAlgorithms.Papers.Independent.Support50.P19.jointQuasiConvexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:30:41.699807+00:00
-- url     : https://prove2.me/theorems/3e39f1dd-6f75-4df6-8ce7-44bea8483056
-- title:
--   Joint quasi-convexity on positive operators
-- statement:
--   Let $1<\alpha\le2$, let $X$ be a finite nonempty index set, let $p_x\ge0$ with $\sum_xp_x=1$, and let $A_x,B_x\ge0$ act on one nonzero finite complex space. Write $A=\sum_xp_xA_x$ and $B=\sum_xp_xB_x$. Then
--   $$\widetilde D_\alpha(A\Vert B)\le\max_{x\in X}\widetilde D_\alpha(A_x\Vert B_x).$$
--   The maximum is taken in the extended real line, so infinite values and zero probabilities are allowed. The operators are not assumed normalized. This controls a mixture by its worst constituent pair.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 15, corollary9

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

/-- PDF p.15, Corollary 9: finite nonempty family of arbitrary positive operators. -/
theorem jointQuasiConvexity [Nonempty I] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (m : ℕ) (hm : 0 < m) (p : Fin m → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (A B : Fin m → Matrix I I ℂ) (hA : ∀ x, (A x).PosSemidef) (hB : ∀ x, (B x).PosSemidef) :
    sandwichedD a (average p A) (average p B) ≤ ⨆ x : Fin m, sandwichedD a (A x) (B x) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
