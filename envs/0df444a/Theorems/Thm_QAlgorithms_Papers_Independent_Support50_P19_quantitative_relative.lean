-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_quantitative_relative
-- name    : QAlgorithms.Papers.Independent.Support50.P19.quantitative_relative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:39:19.775848+00:00
-- url     : https://prove2.me/theorems/5507a65b-b417-45ad-b7f4-de26bfd791f7
-- title:
--   Quantitative comparison near order one
-- statement:
--   Let $\rho,\sigma$ be density operators on a nonzero finite complex space with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Define
--   $$\nu=2^{D_{3/2}(\rho\Vert\sigma)/2}+2^{-D_{1/2}(\rho\Vert\sigma)/2}+1.$$
--   For $1<\alpha<1+\log_2 3/(4\log_2\nu)$,
--   $$\widetilde D_\alpha(\rho\Vert\sigma)\le D(\rho\Vert\sigma)+4(\alpha-1)(\log_2\nu)^2.$$
--   Here $D_t$ denotes Petz divergence in bits, and $D$ ordinary relative entropy. The local definition computes the two powers of two by their equal finite trace expressions, so no infinite divergence is silently converted to a real zero. This estimate controls the limit quantitatively.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 22, eq21

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

/-- PDF p.22, (21), with (20): strict alpha cap and the half factors in renyiNu. -/
theorem quantitative_relative [Nonempty I] (rho sigma : {X : Matrix I I ℂ // IsDensityMatrix X}) (hsupp : Dominates sigma.1 rho.1)
    (a : ℝ) (ha : 1 < a) (hcap : a < 1 + Real.logb 2 3 / (4 * Real.logb 2 (renyiNu rho.1 sigma.1))) :
    sandwichedD a rho.1 sigma.1 ≤ relativeD rho.1 sigma.1 +
      ((4 * (a - 1) * (Real.logb 2 (renyiNu rho.1 sigma.1)) ^ 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
