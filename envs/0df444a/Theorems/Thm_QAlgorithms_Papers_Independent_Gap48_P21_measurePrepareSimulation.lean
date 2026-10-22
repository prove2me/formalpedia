-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_measurePrepareSimulation
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.measurePrepareSimulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:14:40.027588+00:00
-- url     : https://prove2.me/theorems/16ccc4c0-5831-41af-909c-7e85a0af1dc7
-- title:
--   Equation (2): measure/reprepare simulation and its forward cost
-- statement:
--   Let $d\ge2$ and $d/(d+1)\le x\le1$. Alice and Bob share an input-independent Haar-random orthonormal basis. Alice measures the unknown input in this basis, sends the outcome through a $d$-symbol channel that uniformly randomizes with probability $r=(d+1)x-d$, and Bob prepares the received basis state. The averaged channel equals $D_x$ on every operator, including its action on inputs entangled with a reference. The integral defining this average is integrable. Its forward classical cost is
--
--   $${\rm FCCC}_{\rm MR}(D_x)=\log_2d-H_d\!\left(d-x\left(d-\frac1d\right)\right).$$
--
--   The cost is the Shannon capacity of the displayed classical arm. The statement concerns this construction, not a minimum over all possible simulators.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 2, Equation (2): measure/reprepare simulation and its forward cost

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

/-- PDF p.2, Eq.(2): actual common-random-basis simulator, integrability and
its particular forward cost. No minimum over all simulators is asserted. -/
theorem measurePrepareSimulation (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : (d:ℝ)/(d+1) ≤ x) (hx1 : x ≤ 1) :
    let P : Fin d → Fin d → ℝ := randomizing (((d:ℝ)+1)*x-d)
    IsStochastic P ∧
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        ∑ i, ∑ j, ((P i j : ℂ) * (basisProjector U i * X).trace) • basisProjector U j)
        (Schur.unitaryHaar d)) ∧
    measurePrepare d P = QuditFidelity.depolarizingMap d (by omega) x ∧
    kernelCapacity P = Real.logb 2 d - symmetricEntropy d ((d:ℝ)-x*(d-(d:ℝ)⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
