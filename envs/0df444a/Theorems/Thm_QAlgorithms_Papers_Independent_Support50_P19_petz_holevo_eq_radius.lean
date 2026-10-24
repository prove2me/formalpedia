-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_petz_holevo_eq_radius
-- name    : QAlgorithms.Papers.Independent.Support50.P19.petz_holevo_eq_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:34:44.789566+00:00
-- url     : https://prove2.me/theorems/51f2ed64-01f2-4446-a0f6-cc5025dc8337
-- title:
--   Traditional Renyi Holevo information equals its radius
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional channel with nonzero registers and $1<\alpha\le2$. Define $\chi_\alpha$ and $K_\alpha$ by the same ensemble and center optimizations as the sandwiched quantities, but use the unnormalized Petz divergence $D_\alpha$. Then
--   $$\chi_\alpha(\mathcal N)=K_\alpha(\mathcal N).$$
--   The input ensembles contain arbitrary mixed states; extrema are attained. This is a separate identity for traditional relative Renyi entropy, in the range inherited from the preceding proof.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 19, remark15

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

/-- PDF p.19, Remark 15: the same equality for the distinct traditional Petz divergence. -/
theorem petz_holevo_eq_radius [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) :
    channelInformation false a N = informationRadius false a N ∧ InformationExtrema false a N := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
