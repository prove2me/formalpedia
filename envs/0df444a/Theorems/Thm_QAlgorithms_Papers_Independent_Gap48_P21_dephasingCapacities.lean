-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_dephasingCapacities
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.dephasingCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:22:44.593726+00:00
-- url     : https://prove2.me/theorems/4bb91889-8b48-488b-a375-a8a503c17f75
-- title:
--   Unnumbered example: qubit dephasing classical capacities
-- statement:
--   Let $0\le x\le1$. The qubit dephasing channel applies the Pauli operator $\sigma_z$ with probability $x/2$ and otherwise does nothing. Equivalently, it leaves diagonal density-matrix entries unchanged and multiplies off-diagonal entries by $1-x$. Its operational classical capacities obey
--
--   $$C=1,\qquad C_E=2-H_2(x/2).$$
--
--   The assisted model permits unlimited prior pure entanglement and no free classical communication. Thus the assisted values at $x=0$ and $x=1$ are respectively two and one bits per channel use.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered example: qubit dephasing classical capacities

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

/-- PDF p.4: phase flip has probability x/2; the accepted qubit dephasing map
therefore has coherence multiplier 1-x. -/
theorem dephasingCapacities (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (resourceCapacity (finiteMaxEntangled Unit)) (qubitDephasing (1-x)) = 1 ∧
    (resourceCapacity standardEbit) (qubitDephasing (1-x)) = 2-binEntropy2 (x/2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
