-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_binaryProfileExpansion
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.binaryProfileExpansion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:25:22.74161+00:00
-- url     : https://prove2.me/theorems/8b98ddbf-b253-493e-a6ad-53d7bf1038d7
-- title:
--   §VI, unnumbered binary profile series (28)
-- statement:
--   For $0\le x<1$, define $s(x)=\inf_{0<r<1-x}D(\operatorname{diag}(r+x,1-r-x)\|\operatorname{diag}(r,1-r))$, and set $s(1)=+\infty$. The value $s(x)$ is finite for $0<x<1$, and as $x\downarrow0$,
--
--   $$
--   s(x)=2x^2+\frac49x^4+\frac{32}{135}x^6+O(x^8).
--   $$
--
--   This is an expansion of the exact binary minimum, rather than only its Pinsker approximation.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 7, §VI, unnumbered binary profile series (28)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.7, Eq.(28): one-sided expansion of the exact binary minimum. -/
theorem binaryProfileExpansion :
    (∀ x : ℝ, 0 < x → x < 1 → binaryProfile x ≠ ⊤ ∧ binaryProfile x ≠ ⊥) ∧
    (fun x : ℝ => (binaryProfile x).toReal -
      (2 * x ^ 2 + (4 / 9 : ℝ) * x ^ 4 + (32 / 135 : ℝ) * x ^ 6))
      =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] (fun x : ℝ => x ^ 8) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
