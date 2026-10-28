-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_commutingReduction
-- name    : QAlgorithms.Papers.Independent.Support50.P19.commutingReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:26:25.460319+00:00
-- url     : https://prove2.me/theorems/478e4348-5563-4cd7-965f-89eacf4d5b25
-- title:
--   Classical reduction in a common eigenbasis
-- statement:
--   Let $\alpha>1$, let $(|x\rangle)_x$ be any orthonormal basis of a positive-dimensional finite complex space, and let $a_x,b_x\ge0$. Put $A=\sum_xa_x|x\rangle\langle x|$ and $B=\sum_xb_x|x\rangle\langle x|$. Then
--   $$\widetilde D_\alpha(A\Vert B)=D_\alpha(A\Vert B)=\frac1{\alpha-1}\log_2\sum_x a_x^\alpha b_x^{1-\alpha}.$$
--   The right side is $+\infty$ if any $a_x>0$ has $b_x=0$; a term with $a_x=0$ contributes zero, and a zero total has logarithm $-\infty$. Every commuting positive pair has this common-eigenbasis form. This identifies the classical specialization without imposing normalization.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 12, commutingReduction

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

/-- PDF p.12: simultaneous diagonalization in any orthonormal basis gives the classical
unnormalized expression, including unsupported and zero operators. -/
theorem commutingReduction [Nonempty I] (a : ℝ) (ha : 1 < a) (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (U : Matrix.unitaryGroup I ℂ) :
    let A := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) * (U : Matrix I I ℂ)ᴴ
    let B := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (q i : ℂ)) * (U : Matrix I I ℂ)ᴴ
    sandwichedD a A B = petzD a A B ∧ petzD a A B = classicalRenyiBits a p q := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
