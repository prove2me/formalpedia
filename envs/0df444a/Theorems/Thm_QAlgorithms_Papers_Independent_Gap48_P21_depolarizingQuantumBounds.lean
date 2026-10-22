-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_depolarizingQuantumBounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.depolarizingQuantumBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:20:42.001979+00:00
-- url     : https://prove2.me/theorems/8ea22abd-307c-4ebf-9c8f-c12dce362772
-- title:
--   Unnumbered: hashing and erasure bounds on depolarizing Q
-- statement:
--   Let $d\ge2$, $0\le x\le1$, and $N=D_x$ be the $d$-dimensional depolarizing channel. Let $\Phi_d$ be a normalized maximally entangled state of two $d$-dimensional systems, and let $Q(N)$ be the operational unassisted quantum capacity with uniformly vanishing pure-state transmission infidelity. Then
--
--   $$\log_2d-S\!\left((\mathrm{id}\otimes N)(|\Phi_d\rangle\langle\Phi_d|)\right)\le Q(N)\le\max\{0,1-2x\}\log_2d.$$
--
--   The entropy is in bits. The hashing lower expression is signed and may be negative; the upper bound retains the source's maximum with zero. This supplies the interval for $Q$, independently of any entropy formula used to define a capacity.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered: hashing and erasure bounds on depolarizing Q

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

/-- PDF p.4: signed random-hashing lower bound and max-truncated erasure upper
bound for Q. The lower bound is not silently replaced by its positive part. -/
theorem depolarizingQuantumBounds (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let N := QuditFidelity.depolarizingMap d (by omega) x
    Real.logb 2 d - QAlgorithms.Papers.Independent.Dependency50.P45.entropyExchange N
      (chaotic d) ≤ quantumCapacity N ∧
    quantumCapacity N ≤ max 0 (1-2*x)*Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
