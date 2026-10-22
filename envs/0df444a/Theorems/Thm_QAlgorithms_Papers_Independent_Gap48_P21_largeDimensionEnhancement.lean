-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_largeDimensionEnhancement
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.largeDimensionEnhancement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:17:23.063994+00:00
-- url     : https://prove2.me/theorems/3d5b994d-5887-4829-9ed4-bcb4231ee35b
-- title:
--   Unnumbered: large-dimensional enhancement away from full noise
-- statement:
--   Fix $0\le x<1$. For the $d$-dimensional depolarizing channel $D_x$, let $C_E$ denote the operational entanglement-assisted classical capacity and $C_1$ the one-shot accessible classical capacity. Then
--
--   $$\lim_{d\to\infty}\frac{C_E(D_x)}{C_1(D_x)}=2.$$
--
--   The limit is along integer dimensions $d\ge2$. This makes the source's statement about most noise values precise as a pointwise fixed-noise limit; it claims no uniformity near $x=1$.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 3, Unnumbered: large-dimensional enhancement away from full noise

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

/-- PDF p.3: for each fixed noise x<1 the enhancement tends to two as d grows.
The dimension sequence n+2 avoids empty/singleton and log-zero defaults. -/
theorem largeDimensionEnhancement (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ =>
      (resourceCapacity standardEbit) (QuditFidelity.depolarizingMap (n+2) (by omega) x) /
      oneShotCapacity (QuditFidelity.depolarizingMap (n+2) (by omega) x))
      atTop (nhds 2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
