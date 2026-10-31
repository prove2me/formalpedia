-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_rotationalDensity_half_tails
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.rotationalDensity_half_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:03:18.328161+00:00
-- url     : https://prove2.me/theorems/7db4c341-0bb6-421e-9423-4fa55123e6b9
-- title:
--   Lemma 9: rotationally invariant density half-to-half bounds
-- statement:
--   Let $n>0$ and let $Q$ be a measurable probability density on $\mathbb R^{4n}\times\mathbb R^{4n}$ whose law is invariant under $(X,Y)\mapsto(OX,O^TY)$ for every real orthogonal $O$. Write $X=(X_1,X_2)$ and $Y=(Y_1,Y_2)$ in $2n$-coordinate halves. For $0<\epsilon<1$ with $\ln(2/\epsilon)/(2n)\le0.05$, put $t=\sqrt{\ln(2/\epsilon)/(2n)}$. Then
--
--   $$\begin{aligned}
--   \Pr[\|X_2\|^2\ge(1+5t)\|X_1\|^2]&\le\epsilon,\\
--   \Pr[\|Y_2\|^2\ge(1+5t)\|Y_1\|^2]&\le\epsilon,\\
--   \Pr[\langle X_2,Y_2\rangle\le\langle X_1,Y_1\rangle-\tfrac92t(\|X_1\|^2+\|Y_1\|^2)]&\le2\epsilon,\\
--   \Pr[\|X_2\|^2\le(1-4t)\|X_1\|^2]&\le\epsilon,\\
--   \Pr[\|Y_2\|^2\le(1-4t)\|Y_1\|^2]&\le\epsilon.
--   \end{aligned}$$
--
--   The final two bounds are supporting conclusions displayed in the proof. The literal real symmetry is retained; no implication from the physical passive unitary twirl is asserted. The density condition excludes atoms at the all-zero pair.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 22, Lemma 9, E14–E16 and E18–E19

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.22, Lemma 9 (E14–E16), including supporting E18–E19.
Q is an actual probability density. The coefficient in E16 is 9/2;
the erroneous intermediate E17 is not assumed. -/
theorem rotationalDensity_half_tails
    (n : ℕ) (hn : 0 < n)
    (q : ((Fin (4 * n) → ℝ) × (Fin (4 * n) → ℝ)) → ℝ≥0∞)
    (hq : Measurable q) [IsProbabilityMeasure (pairDensityLaw n q)]
    (hinv : ∀ O : Matrix.unitaryGroup (Fin (4 * n)) ℝ,
      Measure.map (transposeRotation O) (pairDensityLaw n q) = pairDensityLaw n q)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon < 1)
    (hregime : Real.log (2 / epsilon) / (2 * n) ≤ 0.05) :
    let law := pairDensityLaw n q
    let t := Real.sqrt (Real.log (2 / epsilon) / (2 * n))
    let first := fun v : Fin (4 * n) → ℝ => firstCoordinates (2 * n) v
    let second := fun v : Fin (4 * n) → ℝ => v - first v
    law {v | vectorSquare (second v.1) ≥ (1 + 5 * t) * vectorSquare (first v.1)} ≤
      ENNReal.ofReal epsilon ∧
    law {v | vectorSquare (second v.2) ≥ (1 + 5 * t) * vectorSquare (first v.2)} ≤
      ENNReal.ofReal epsilon ∧
    law {v | realDot (second v.1) (second v.2) ≤ realDot (first v.1) (first v.2) -
      (9 / 2 : ℝ) * t * (vectorSquare (first v.1) + vectorSquare (first v.2))} ≤
      ENNReal.ofReal (2 * epsilon) ∧
    law {v | vectorSquare (second v.1) ≤ (1 - 4 * t) * vectorSquare (first v.1)} ≤
      ENNReal.ofReal epsilon ∧
    law {v | vectorSquare (second v.2) ≤ (1 - 4 * t) * vectorSquare (first v.2)} ≤
      ENNReal.ofReal epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
