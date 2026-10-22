-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_highNoiseEnhancement
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.highNoiseEnhancement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:16:31.520935+00:00
-- url     : https://prove2.me/theorems/30b155c5-d8f4-4de1-827f-72082a9b6aaa
-- title:
--   Unnumbered: enhancement approaches d+1 and is unbounded
-- statement:
--   For each integer $d\ge2$, let $C_E(D_x)$ be the assisted operational capacity of the $d$-dimensional depolarizing channel and $C_1(D_x)$ its optimal one-shot accessible capacity. Approaching full noise from below within the allowed interval,
--
--   $$\lim_{x\to1^-}\frac{C_E(D_x)}{C_1(D_x)}=d+1.$$
--
--   Moreover, for every real number $K$ there exist an integer $d\ge2$ and $0\le x<1$ with $C_1(D_x)>0$ and $C_E(D_x)/C_1(D_x)>K$. The comparison is with $C_1$, the best known unassisted rate in this source, and excludes the zero-over-zero endpoint.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 3, Unnumbered: enhancement approaches d+1 and is unbounded

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

/-- PDF p.3, following Eq.(3): high-noise limit relative to C1, and unbounded
factors as dimensions vary. The endpoint x=1 is excluded from every ratio. -/
theorem highNoiseEnhancement :
    (∀ d : ℕ, ∀ hd : 2 ≤ d,
      Tendsto (fun x => (resourceCapacity standardEbit) (QuditFidelity.depolarizingMap d (by omega) x) /
        oneShotCapacity (QuditFidelity.depolarizingMap d (by omega) x))
        (nhdsWithin 1 (Set.Ico (0:ℝ) 1)) (nhds ((d:ℝ)+1))) ∧
    (∀ K : ℝ, ∃ d : ℕ, ∃ hd : 2 ≤ d, ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧
      0 < oneShotCapacity (QuditFidelity.depolarizingMap d (by omega) x) ∧
      K < (resourceCapacity standardEbit) (QuditFidelity.depolarizingMap d (by omega) x) /
        oneShotCapacity (QuditFidelity.depolarizingMap d (by omega) x)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
