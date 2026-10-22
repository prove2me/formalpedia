-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_classicalLargeDimensionGap
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.classicalLargeDimensionGap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:20:00.644988+00:00
-- url     : https://prove2.me/theorems/694ece10-ab96-4d8d-a622-d2a2db88e693
-- title:
--   Unnumbered: classical bound difference tends to binary entropy
-- statement:
--   Fix $0\le x\le1$. Let $C_1(D_x^{(d)})$ and $C(D_x^{(d)})$ be the one-shot accessible and operational unassisted capacities in dimension $d$. The gap between the source's classical bounds satisfies
--
--   $$\lim_{d\to\infty}\left[(1-x)\log_2d-C_1(D_x^{(d)})\right]=H_2(x).$$
--
--   If $x<1$, the same gap divided by $C(D_x^{(d)})$ tends to zero. Here $H_2(x)=-x\log_2x-(1-x)\log_2(1-x)$ in bits. The absolute limit includes $x=0,1$; only the relative assertion excludes full noise, where the capacity is zero.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Unnumbered: classical bound difference tends to binary entropy

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

/-- PDF p.4: absolute classical-bound gap tends to H2(x), including both
endpoints. Its ratio to C tends to zero for fixed x<1 only. -/
theorem classicalLargeDimensionGap (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun n : ℕ => (1-x)*Real.logb 2 (n+2) -
      oneShotCapacity (QuditFidelity.depolarizingMap (n+2) (by omega) x))
      atTop (nhds (binEntropy2 x)) ∧
    (x < 1 → Tendsto (fun n : ℕ =>
      ((1-x)*Real.logb 2 (n+2) -
        oneShotCapacity (QuditFidelity.depolarizingMap (n+2) (by omega) x)) /
        (resourceCapacity (finiteMaxEntangled Unit)) (QuditFidelity.depolarizingMap (n+2) (by omega) x))
      atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
