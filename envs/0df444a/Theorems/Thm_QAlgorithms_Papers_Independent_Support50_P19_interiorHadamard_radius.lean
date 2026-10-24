-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_interiorHadamard_radius
-- name    : QAlgorithms.Papers.Independent.Support50.P19.interiorHadamard_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:43:54.618415+00:00
-- url     : https://prove2.me/theorems/6742aa86-f11b-48e6-9052-c3357abbc239
-- title:
--   Fixed-center subadditivity for interior Hadamard channels
-- statement:
--   Let $\mathcal N_H:A\to B$ be a channel on nonzero finite complex spaces that has an entanglement-breaking complementary channel in the relative interior of the EB channels, relative to the affine space of trace-preserving Hermiticity-preserving maps. For every output density center $\sigma$ there exists $\eta>0$, depending only on the channel and center, such that for every $1<\alpha<1+\eta$ and every integer $n\ge1$,
--   $$\frac1n\widetilde K_\alpha^{[\sigma^{\otimes n}]}(\mathcal N_H^{\otimes n})\le\widetilde K_\alpha^{[\sigma]}(\mathcal N_H).$$
--   The two channels in the complementary description use the same Stinespring isometry. Singular compatible centers are interpreted on essential output support; incompatible centers give infinite radii. This is the qualified local-order intermediate result, distinct from the unrestricted final strong converse.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 25, interiorHadamardRadius

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

/-- PDF pp.25–26: fixed-center subadditivity near one for an interior-EB complement.
The neighborhood depends on the channel and center, and precedes every blocklength.
Singular compatible centers are interpreted on essential output support as on p.25. -/
theorem interiorHadamard_radius [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N)
    (hint : InteriorHadamard N) (sigma : {X : Matrix J J ℂ // IsDensityMatrix X}) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ a : ℝ, 1 < a → a < 1 + eta →
      ∀ n : ℕ, 0 < n →
        ((1 / (n : ℝ) : ℝ) : EReal) *
          fixedRadius true a (channelPower N n) (tensorPower n sigma.1) ≤
            fixedRadius true a N sigma.1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
