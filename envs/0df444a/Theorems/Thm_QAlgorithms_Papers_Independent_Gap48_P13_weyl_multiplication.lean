-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_weyl_multiplication
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.weyl_multiplication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:38:31.778349+00:00
-- url     : https://prove2.me/theorems/999ec0e4-d783-4214-b291-29ed93507eae
-- title:
--   Weyl multiplication with the positive cocycle
-- statement:
--   On the complete oscillator Hilbert space let $a\phi_n=\sqrt n\phi_{n-1}$ and $a^+\phi_n=\sqrt{n+1}\phi_{n+1}$. Define $W(z)=\exp(za-\overline z a^+)$ through the self-adjoint generator closure. For every $z,w\in\mathbb C$,
--
--   $$W(z)W(w)=\exp\!\left(i\operatorname{Im}(\overline z w)\right)W(z+w).$$
--
--   Each operator is its unitary realization with the complete number-basis coefficients. This identifies the precise CCR cocycle used throughout the paper.
--
--   **Formalization Note** The accepted displacement convention is $D(\alpha)=\exp(\alpha a^+-\overline\alpha a)$, so $W(z)=D(-\overline z)$. Realization is concluded, not assumed.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 5, Theorem 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

/-- Theorem 1.1, PDF p.5: the positive Weyl cocycle, for the actual operators of (12).
The realization clauses discharge the accepted operator-selection fallback. -/
theorem weyl_multiplication (z w : ℂ) :
    (∀ v : ℂ, (Osc.HasFockMatrix (Osc.displacement (-star v)) (Osc.displacementMatrix (-star v)) ∧
      (ContinuousLinearMap.adjoint (Osc.displacement (-star v))).comp (Osc.displacement (-star v)) = 1 ∧
      (Osc.displacement (-star v)).comp (ContinuousLinearMap.adjoint (Osc.displacement (-star v))) = 1)) ∧
    (Osc.displacement (-star z)).comp (Osc.displacement (-star w)) =
      Complex.exp (Complex.I * ((star z * w).im : ℂ)) • (Osc.displacement (-star (z + w))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
