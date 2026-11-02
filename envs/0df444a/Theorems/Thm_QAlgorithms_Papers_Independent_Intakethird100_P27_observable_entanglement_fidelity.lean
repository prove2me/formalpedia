-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_observable_entanglement_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.observable_entanglement_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:14:46.79576+00:00
-- url     : https://prove2.me/theorems/40ef86b1-df9a-495d-9cd6-cb57244c6088
-- title:
--   Observable distortion equals one minus source entanglement fidelity
-- statement:
--   Let $A$ be a finite nonempty register, let $\psi_{RA}$ be a unit vector with $R$ isomorphic to $A$, and let $\mathcal N:A\to A$ be CPTP. Write $P=|\psi\rangle\langle\psi|$, $\omega=(\mathrm{id}_R\otimes\mathcal N)(P)$, and $F_e=\langle\psi|\omega|\psi\rangle$. Then $I-P$ is positive semidefinite and
--
--   $$\operatorname{Tr}[(I-P)\omega]=1-F_e.$$
--
--   Thus the general positive-observable distortion model includes the original entanglement-fidelity distortion for any source density, including rank-deficient sources.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 5, Example 6

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

/-- PDF p.5, Example 6: I-|psi><psi| is a positive observable and its expected
distortion is exactly one minus the general source entanglement fidelity. -/
theorem observable_entanglement_fidelity {A : Type} [Fintype A] [Nonempty A]
    (v : EuclideanSpace ℂ (A × A)) (hv : ‖v‖ = 1)
    (N : Superop A A) (hN : IsChannel N) :
    (1 - pureDensity v).PosSemidef ∧
      effectProb (1 - pureDensity v) (idTensorSuperop N (pureDensity v)) =
        1 - sourceFidelity v N := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
