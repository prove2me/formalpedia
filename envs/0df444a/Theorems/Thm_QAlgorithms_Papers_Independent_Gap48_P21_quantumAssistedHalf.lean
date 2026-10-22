-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_quantumAssistedHalf
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.quantumAssistedHalf
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:23:54.024093+00:00
-- url     : https://prove2.me/theorems/fe05dba8-596d-4146-bc40-7580194a8fd6
-- title:
--   Unnumbered: QE=CE/2 and Q<=QE
-- statement:
--   Let $N$ be a completely positive trace-preserving channel between nonzero finite-dimensional complex systems. Define $Q(N)$ and $Q_E(N)$ operationally by uniformly vanishing pure-state transmission infidelity, without a classical side channel, using respectively no prior entanglement and unlimited prior EPR pairs. Let $C_E(N)$ be its operational assisted classical capacity. Then
--
--   $$Q_E(N)=\tfrac12 C_E(N),\qquad Q(N)\le Q_E(N).$$
--
--   Both rate conversions are retained: any achievable assisted quantum rate $R$ gives an assisted classical rate $2R$, and any achievable assisted classical rate $R$ gives an assisted quantum rate $R/2$. These express the two protocols behind the capacity identity.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered: QE=CE/2 and Q<=QE

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P21

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.Elementwise

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Gap48.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Reuse the finite Pi-space extended norm explicitly. Matrix has the same
-- product topology, but the generic instance search did not bridge the alias.

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P21.matrixContinuousENorm

open QAlgorithms.Papers.Independent.Dependency50.P45
  (resourceCapacity standardEbit DMC shannonCapacity blockProb)

open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl chaotic)

open QAlgorithms.Papers.Independent.Information100.P58 (singleErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

-- CE uses resourceCapacity standardEbit directly; C uses the same accepted
-- operational capacity with the one-dimensional product resource.

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

/-- PDF p.4: both classical/quantum conversion directions and Q<=QE, with
independently defined capacities and no classical side channel for QE. -/
theorem quantumAssistedHalf {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) :
    ebitTransmissionCapacity N = (resourceCapacity standardEbit) N / 2 ∧
    quantumCapacity N ≤ ebitTransmissionCapacity N ∧
    (∀ R : ℝ, EbitTransmissionAchievable N R →
      QAlgorithms.Papers.Independent.Dependency50.P45.AchievableWith standardEbit N
        (fun {_ _} _ => True) (2*R)) ∧
    (∀ R : ℝ, QAlgorithms.Papers.Independent.Dependency50.P45.AchievableWith standardEbit N
        (fun {_ _} _ => True) R → EbitTransmissionAchievable N (R/2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
