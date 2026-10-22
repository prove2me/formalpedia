-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_binaryProfileBounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.binaryProfileBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:26:18.899989+00:00
-- url     : https://prove2.me/theorems/34f03cc5-cdff-4ee9-ad1a-b2f63a3b72e2
-- title:
--   §VI, unnumbered scalar profile estimates and endpoint divergence
-- statement:
--   For $0\le x<1$, define $s(x)=\inf_{0<r<1-x}D(\operatorname{diag}(r+x,1-r-x)\|\operatorname{diag}(r,1-r))$, and set $s(1)=+\infty$. For every $0\le x<1$,
--
--   $$
--   2x^2\le s(x)\le-\log(1-x),\qquad\lim_{x\uparrow1}s(x)=+\infty.
--   $$
--
--   Moreover $s(1)=+\infty$, and if $Cx^2\le s(x)$ for every $0<x<1$, then $C\le2$.
--
--   The lower coefficient 2 is optimal among global quadratic bounds; the upper estimate gives the stated endpoint comparison.
--
--   The boundary value of the binary objective is retained explicitly: for each $0≤x<1$, as $r$ increases to $1-x$ through $0<r<1-x$, its relative entropy tends to $-\log(1-x)$.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 7, §VI, unnumbered scalar profile estimates and endpoint divergence

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

/-- PDF p.7: profile estimates, sharp quadratic coefficient, and endpoint divergence. -/
theorem binaryProfileBounds :
    (∀ x : ℝ, 0 ≤ x → x < 1 →
      ((2 * x ^ 2 : ℝ) : EReal) ≤ binaryProfile x ∧
        binaryProfile x ≤ ((-Real.log (1 - x) : ℝ) : EReal) ∧
        Tendsto (fun r : ℝ => relativeEntropy (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)]))
          (nhdsWithin (1 - x) (Set.Ioo 0 (1 - x)))
          (nhds ((-Real.log (1 - x) : ℝ) : EReal))) ∧
    Tendsto binaryProfile (nhdsWithin 1 (Set.Iio 1)) (nhds ⊤) ∧
    binaryProfile 1 = ⊤ ∧
    (∀ C : ℝ, (∀ x : ℝ, 0 < x → x < 1 →
      ((C * x ^ 2 : ℝ) : EReal) ≤ binaryProfile x) → C ≤ 2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
