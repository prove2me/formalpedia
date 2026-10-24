-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_radius_near_one
-- name    : QAlgorithms.Papers.Independent.Support50.P19.radius_near_one
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:40:01.367999+00:00
-- url     : https://prove2.me/theorems/9d15bd86-9a14-4432-9962-6a6fab5d7a7b
-- title:
--   Uniform channel-radius estimate near one
-- statement:
--   Let $\mathcal N_{\rm EB}$ be a finite-dimensional entanglement-breaking channel with nonzero registers. There exist a density operator $\sigma_*$ and a finite real constant $c>1$ such that $\sigma_*$ attains the ordinary information-radius minimum, contains every output support, and $\nu(\mathcal N_{\rm EB}(\rho),\sigma_*)\le c$ for every input density $\rho$. For every $1<\alpha<1+\log_2 3/(4\log_2c)$,
--   $$\widetilde K_\alpha(\mathcal N_{\rm EB})\le\chi(\mathcal N_{\rm EB})+4(\alpha-1)(\log_2c)^2.$$
--   The center and constant precede alpha and all input data. This is a uniform approximation by the single-letter Holevo information, not an assumption about arbitrary comparison states.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 22, eq23

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

/-- PDF pp.22–23, (23): an attained center and finite c chosen before all alpha and input data. -/
theorem radius_near_one [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N) (hEB : IsEB N) :
    ∃ sigma : Matrix J J ℂ, ∃ c : ℝ, CenterControl N sigma c ∧
      ∀ a : ℝ, 1 < a → a < 1 + Real.logb 2 3 / (4 * Real.logb 2 c) →
        informationRadius true a N ≤
          (((QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 N) + 4 * (a - 1) * (Real.logb 2 c) ^ 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
