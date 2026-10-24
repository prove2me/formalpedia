-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_minimumOutput_converse
-- name    : QAlgorithms.Papers.Independent.Support50.P19.minimumOutput_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:42:28.638121+00:00
-- url     : https://prove2.me/theorems/cb891a83-41a3-4639-99c6-8506ed62a600
-- title:
--   Strong-converse threshold from minimum-output entropy additivity
-- statement:
--   Let $\mathcal N:A\to B$ be any channel on nonzero finite complex spaces, and put $d=\dim B$. For $\alpha\ge1$, let $H_\alpha^{\min}(\mathcal N)=\min_\rho H_\alpha(\mathcal N(\rho))$, with $H_1$ the von Neumann entropy in bits. Suppose that for every $\alpha\ge1$ and every integer $n\ge1$,
--   $$H_\alpha^{\min}(\mathcal N^{\otimes n})=nH_\alpha^{\min}(\mathcal N).$$
--   Then $T=\log_2d-H_1^{\min}(\mathcal N)$ is an exponential strong-converse threshold: for every $R>T$ there exist $c>0,n_0\ge1$ such that all $n\ge n_0$ use unassisted codes of actual rate at least $R$ obey $p_{\rm succ}\le2^{-cn}$. The constants precede all codes. This is a threshold statement for arbitrary channels; it does not identify $T$ with operational capacity.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 24, minimumOutputStrongConverse

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

/-- PDF p.24, final paragraph of 8.1: general entropy-additivity strong-converse threshold.
No covariance or claim of equality with capacity is imposed. -/
theorem minimumOutput_converse [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N)
    (hadd : ∀ a : ℝ, 1 ≤ a → ∀ n : ℕ, 0 < n →
      minOutput a (channelPower N n) = (n : ℝ) * minOutput a N) :
    ExponentialAt N (Real.logb 2 (Fintype.card J) - minOutput 1 N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
