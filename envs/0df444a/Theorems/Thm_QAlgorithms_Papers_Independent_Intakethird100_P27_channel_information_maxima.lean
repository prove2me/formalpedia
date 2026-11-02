-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_channel_information_maxima
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.channel_information_maxima
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:18:19.695374+00:00
-- url     : https://prove2.me/theorems/8f5bedf6-aa60-4eeb-89ae-79e32cecd6bb
-- title:
--   Equality of attained ordinary and conditional channel-information maxima
-- statement:
--   Let $\mathcal N:A\to B'$ be a fixed CPTP channel between finite nonempty registers. Both optimizations below range over normalized pure states, and all entropies are in bits. On the left, the purifying reference may be chosen isomorphic to $A$. On the right, the reference $R$ and side register $B$ may be arbitrary finite nonempty systems. The channel acts only on $A$. Then both maxima are attained and
--
--   $$\max_{\psi_{RA}}I(R;B')_{(\mathrm{id}\otimes\mathcal N)(\psi)}=\max_{\phi_{RAB}}I(R;B'\mid B)_{(\mathrm{id}\otimes\mathcal N\otimes\mathrm{id})(\phi)}.$$
--
--   The common value is achieved on the right with a product pure one-dimensional side register. The upper bound still covers every side register and every pure input.
--
--   This identifies channel information quantities; it does not assert the conjectured general-input operational simulation theorem (40).
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 14, Theorem 15, proof continues p.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P27

open Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRB mutualInformation bipartiteBlock epr)

open QAlgorithms.Papers.Independent.Information100.P08 (formation)

open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

open QAlgorithms.Papers.Independent.Bridge50.P37 (isotropicState normalizedEntangledProjection)

/-- PDF pp.14--15, Theorem 15: the ordinary and conditional channel-information
maxima have a common attained value. The ordinary reference is isomorphic to A;
the conditional upper bound ranges over arbitrary nonempty finite reference and
side-register types. A product pure one-dimensional side register attains it.
The conjectured general-input simulation theorem (40) is not asserted. -/
theorem channel_information_maxima {A C : Type} [Fintype A] [Fintype C]
    [Nonempty A] [Nonempty C] (N : Superop A C) (hN : IsChannel N) :
    ∃ v : EuclideanSpace ℂ (A × A), ‖v‖ = 1 ∧
      (∀ w : EuclideanSpace ℂ (A × A), ‖w‖ = 1 →
        mutualInformation (idTensorSuperop N (pureDensity w)) ≤
          mutualInformation (idTensorSuperop N (pureDensity v))) ∧
      (∃ phi : EuclideanSpace ℂ (A × (A × Fin 1)), ‖phi‖ = 1 ∧
        conditionalOutputInformation N phi =
          mutualInformation (idTensorSuperop N (pureDensity v))) ∧
      (∀ (R B : Type) [Fintype R] [Fintype B] [Nonempty R] [Nonempty B],
        ∀ phi : EuclideanSpace ℂ (R × (A × B)), ‖phi‖ = 1 →
          conditionalOutputInformation N phi ≤
            mutualInformation (idTensorSuperop N (pureDensity v))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
