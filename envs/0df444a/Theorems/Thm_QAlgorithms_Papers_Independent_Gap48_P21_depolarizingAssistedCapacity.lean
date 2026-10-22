-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_depolarizingAssistedCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.depolarizingAssistedCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:13:03.723478+00:00
-- url     : https://prove2.me/theorems/a4a1e354-5b7a-4311-a700-e6e397058097
-- title:
--   Abstract main result / equation (3): depolarizing assisted capacity
-- statement:
--   Let $d\ge2$ be an integer and $0\le x\le1$. The depolarizing channel is $D_x(\rho)=(1-x)\rho+xI/d$. Let $C_E$ denote its operational classical capacity with unlimited prior pure entanglement and no free classical communication. Standard dense coding through $D_x$ induces the $d^2$-symbol channel that replaces its input by a uniform symbol with probability $x$. Noisy teleportation using that classical arm reproduces $D_x$ exactly. Consequently,
--
--   $$C_E(D_x)=C_{\rm Sd}(D_x)={\rm FCCC}_{\rm Tp}(D_x)=2\log_2d-H_{d^2}\!\left(1-x\frac{d^2-1}{d^2}\right).$$
--
--   Here $H_m(p)=-p\log_2p-(1-p)\log_2((1-p)/(m-1))$, with zero logarithmic terms interpreted as zero. The forward cost is the Shannon capacity of this exhibited classical arm. This identifies the capacity by matching an achievable protocol with an actual simulator.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 3, Abstract main result / equation (3): depolarizing assisted capacity

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

/-- PDF p.3, Eq.(3): CE, the fixed dense-coding rate and the forward Shannon cost
of the exhibited teleportation simulator all equal the displayed entropy formula. -/
theorem depolarizingAssistedCapacity (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let N := QuditFidelity.depolarizingMap d (by omega) x
    let P := denseKernel d (by omega) N
    IsStochastic P ∧ P = randomizing x ∧ teleportMap d (by omega) P = N ∧
    (resourceCapacity standardEbit) N = denseRate d (by omega) N ∧
    (resourceCapacity standardEbit) N = kernelCapacity P ∧
    (resourceCapacity standardEbit) N = 2 * Real.logb 2 d -
      symmetricEntropy (d^2) (1-x*((d:ℝ)^2-1)/(d:ℝ)^2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
