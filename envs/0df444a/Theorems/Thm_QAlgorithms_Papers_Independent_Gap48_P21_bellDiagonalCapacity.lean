-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_bellDiagonalCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.bellDiagonalCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:21:41.581194+00:00
-- url     : https://prove2.me/theorems/431f8f97-796b-4d15-9f86-2407aa508ea1
-- title:
--   Unnumbered: Bell-diagonal capacity via the protocol round trip
-- statement:
--   Let $d\ge2$ and let $N$ be a completely positive trace-preserving channel on a $d$-dimensional complex system. Let $\mathrm{Sd}(N)$ be the classical channel from the fixed dense-coding protocol and $\mathrm{Tp}(P)$ the actual channel implemented by teleportation through a classical arm $P$. Assume the operational Bell-diagonal condition
--
--   $$\mathrm{Tp}(\mathrm{Sd}(N))=N.$$
--
--   Then
--
--   $$C_E(N)=C_{\rm Sd}(N)={\rm FCCC}_{\rm Tp}(N)=C(\mathrm{Sd}(N)).$$
--
--   Here the forward cost belongs to this round-trip simulator. The hypothesis is an equality of constructed maps on operators and does not assume any capacity equality.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered: Bell-diagonal capacity via the protocol round trip

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

/-- PDF p.4: Bell diagonal is the operational ROUND TRIP, never a predicate
asserting the capacity equality that this theorem is meant to conclude. -/
theorem bellDiagonalCapacity (d : ℕ) (hd : 2 ≤ d)
    (N : Superop (Fin d) (Fin d)) (hN : IsChannel N)
    (hround : teleportMap d (by omega) (denseKernel d (by omega) N) = N) :
    (resourceCapacity standardEbit) N = denseRate d (by omega) N ∧
    (resourceCapacity standardEbit) N = kernelCapacity (denseKernel d (by omega) N) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
