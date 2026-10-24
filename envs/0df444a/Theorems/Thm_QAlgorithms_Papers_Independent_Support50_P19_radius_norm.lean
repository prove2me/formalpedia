-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_radius_norm
-- name    : QAlgorithms.Papers.Independent.Support50.P19.radius_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:35:38.276177+00:00
-- url     : https://prove2.me/theorems/ab16866a-0122-42fc-91ca-f8cf31227c3e
-- title:
--   Weighted-norm representation of the sandwiched radius
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional channel with nonzero registers and let $\alpha>1$. For $X\ge0$ write $\|Z\|_{\alpha,X}=\|X^{1/2}ZX^{1/2}\|_\alpha$, where $\|\cdot\|_\alpha$ is the Schatten alpha-norm. Let $\mathcal S_{\mathcal N}$ consist of density centers $\sigma$ whose support contains every channel output support. Then
--   $$\widetilde K_\alpha(\mathcal N)=\min_{\sigma\in\mathcal S_{\mathcal N}}\max_\rho\frac\alpha{\alpha-1}\log_2\|\mathcal N(\rho)\|_{\alpha,\sigma^{(1-\alpha)/\alpha}}=\min_{\sigma\in\mathcal S_{\mathcal N}}\frac\alpha{\alpha-1}\log_2\max_\rho\|\mathcal N(\rho)\|_{\alpha,\sigma^{(1-\alpha)/\alpha}}.$$
--   Input optimizations range over density operators. Incompatible centers have infinite divergence and are excluded from this finite inverse-support expression; singular compatible centers remain allowed. This form links the radius to output-norm multiplicativity.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 19, normRadius

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

/-- PDF p.19, (16): both norm orders, using the finite inverse-support domain. -/
theorem radius_norm [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a) (N : Superop I J) (hN : IsChannel N) :
    informationRadius true a N = normRadiusBefore a N ∧
    normRadiusBefore a N = normRadiusAfter a N ∧ NormExtrema a N := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
