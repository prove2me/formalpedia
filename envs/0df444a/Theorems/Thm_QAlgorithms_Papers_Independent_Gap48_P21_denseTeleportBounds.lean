-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_denseTeleportBounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.denseTeleportBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:15:41.244875+00:00
-- url     : https://prove2.me/theorems/ff199207-4fee-4800-8a91-67d6c7d042cd
-- title:
--   Figure 2: noisy dense-coding lower and teleportation upper bounds
-- statement:
--   Let $d\ge2$ and let $N$ be a completely positive trace-preserving channel on a $d$-dimensional complex system. Define $C_{\rm Sd}(N)$ as the Shannon capacity of the classical transition matrix obtained from the fixed maximally entangled dense-coding encoder and Bell measurement. Then
--
--   $$C_{\rm Sd}(N)\le C_E(N).$$
--
--   For every stochastic $d^2$-symbol classical transition matrix $P$ whose noisy-teleportation construction actually equals $N$, one also has
--
--   $$C_E(N)\le C(P).$$
--
--   Here $C(P)$ is the Shannon capacity of that classical arm and hence the forward cost of this simulator. The upper bound is conditional on the constructed map equality, so an arbitrary assigned cost is insufficient.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 3, Figure 2: noisy dense-coding lower and teleportation upper bounds

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

/-- PDF p.3, Fig.2: fixed dense-coding lower bound; teleportation upper bound
only for a stochastic classical arm that actually implements N. -/
theorem denseTeleportBounds (d : ℕ) (hd : 2 ≤ d)
    (N : Superop (Fin d) (Fin d)) (hN : IsChannel N) :
    denseRate d (by omega) N ≤ (resourceCapacity standardEbit) N ∧
    ∀ P : (Fin d × Fin d) → (Fin d × Fin d) → ℝ,
      IsStochastic P → teleportMap d (by omega) P = N →
      (resourceCapacity standardEbit) N ≤ kernelCapacity P := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
