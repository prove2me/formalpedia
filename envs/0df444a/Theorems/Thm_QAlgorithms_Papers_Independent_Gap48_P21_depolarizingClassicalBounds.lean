-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_depolarizingClassicalBounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.depolarizingClassicalBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:18:58.37598+00:00
-- url     : https://prove2.me/theorems/f48e78e6-e99e-4995-ae58-05b601556dea
-- title:
--   Unnumbered: interval for unknown depolarizing classical capacity
-- statement:
--   Let $d\ge2$, $0\le x\le1$, and $D_x(\rho)=(1-x)\rho+xI/d$. Write $C$ for its operational unassisted classical capacity with arbitrary entangled block inputs and collective decoding, $C_1$ for its one-shot accessible capacity, and $C_E$ for its capacity with unlimited prior pure entanglement. Then
--
--   $$C_1(D_x)\le C(D_x)\le\min\{C_E(D_x),(1-x)\log_2d\}.$$
--
--   This records exactly the source's interval for the unknown unassisted capacity, without replacing it by a later additivity result.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered: interval for unknown depolarizing classical capacity

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

/-- PDF pp.3--4: the source's interval for C; no later C=C1 result is inserted. -/
theorem depolarizingClassicalBounds (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let N := QuditFidelity.depolarizingMap d (by omega) x
    oneShotCapacity N ≤ (resourceCapacity (finiteMaxEntangled Unit)) N ∧
    (resourceCapacity (finiteMaxEntangled Unit)) N ≤ (resourceCapacity standardEbit) N ∧
    (resourceCapacity (finiteMaxEntangled Unit)) N ≤ (1-x)*Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
