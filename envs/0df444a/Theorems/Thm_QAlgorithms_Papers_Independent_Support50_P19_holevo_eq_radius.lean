-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_holevo_eq_radius
-- name    : QAlgorithms.Papers.Independent.Support50.P19.holevo_eq_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:33:47.768981+00:00
-- url     : https://prove2.me/theorems/5de88ae7-a01b-4394-a907-8f1608086084
-- title:
--   Alpha-Holevo information equals alpha-information radius
-- statement:
--   Let $\mathcal N:A\to B$ be a channel on positive-dimensional finite complex spaces and $1<\alpha\le2$. Optimize over all finite ensembles of mixed input density operators and all output density centers. Then
--   $$\widetilde\chi_\alpha(\mathcal N):=\max_{\{p_x,\rho_x\}}\min_\sigma\widetilde D_\alpha(\omega_{XB}\Vert\omega_X\otimes\sigma)=\min_\sigma\max_\rho\widetilde D_\alpha(\mathcal N(\rho)\Vert\sigma)=:\widetilde K_\alpha(\mathcal N),$$
--   where $\omega_{XB}=\sum_xp_x|x\rangle\langle x|\otimes\mathcal N(\rho_x)$. The maximizing ensemble, minimizing center, and each fixed-center maximizing input are attained. The equality supplies the full min–max interface used in subadditivity.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 18, lemma14

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

/-- PDF pp.18–19, Lemma 14: mixed-ensemble max-min equals the full min-max radius. -/
theorem holevo_eq_radius [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (N : Superop I J) (hN : IsChannel N) :
    channelInformation true a N = informationRadius true a N ∧ InformationExtrema true a N := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
