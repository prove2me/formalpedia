-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_erasureAssistedCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.erasureAssistedCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:18:10.171532+00:00
-- url     : https://prove2.me/theorems/5d4d2ce0-afad-421a-baa4-d6c17db41a57
-- title:
--   Unnumbered: erasure assisted capacity and coincidence of protocol bounds
-- statement:
--   Let $d\ge1$ and $0\le x\le1$. The quantum erasure channel $E_x$ transmits a $d$-dimensional input intact with probability $1-x$ and otherwise emits a single orthogonal flag, so its output dimension is $d+1$. Dense coding through $E_x$ induces the classical erasure channel on $d^2$ messages, and teleportation with this classical arm reproduces $E_x$. Their achievable rate and forward cost coincide, giving
--
--   $$C_E(E_x)=C_{\rm Sd}(E_x)={\rm FCCC}_{\rm Tp}(E_x)=2(1-x)\log_2d=2C(E_x),\qquad C(E_x)=(1-x)\log_2d.$$
--
--   Capacities are operational with vanishing error; assistance consists of unlimited prior pure entanglement, without a free classical side channel. The one-dimensional input and both noise endpoints are included.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 3, Unnumbered: erasure assisted capacity and coincidence of protocol bounds

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

/-- PDF p.3: erasure dense coding and noisy teleportation coincide, and their
common capacity is twice the ordinary classical capacity. Output dimension d+1. -/
theorem erasureAssistedCapacity (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let P := erasureDenseKernel d (by omega) x
    IsStochastic P ∧ P = classicalErasure x ∧
    erasureTeleportMap d (by omega) P = singleErasure d x ∧
    (resourceCapacity standardEbit) (singleErasure d x) = kernelCapacity P ∧
    (resourceCapacity standardEbit) (singleErasure d x) = 2*(1-x)*Real.logb 2 d ∧
    (resourceCapacity (finiteMaxEntangled Unit)) (singleErasure d x) = (1-x)*Real.logb 2 d ∧
    (resourceCapacity standardEbit) (singleErasure d x) = 2*(resourceCapacity (finiteMaxEntangled Unit)) (singleErasure d x) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
