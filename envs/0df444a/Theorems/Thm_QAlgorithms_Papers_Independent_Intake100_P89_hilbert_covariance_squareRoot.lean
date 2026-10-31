-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_hilbert_covariance_squareRoot
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.hilbert_covariance_squareRoot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:37:26.381065+00:00
-- url     : https://prove2.me/theorems/771de758-6788-42ee-bcf7-1c5829f0d6f6
-- title:
--   Example 2.1: Hilbert covariance square root
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a separable real Hilbert space $B$. Its covariance operator $S$ is continuous linear, positive, self-adjoint and has finite trace. It admits a positive self-adjoint square root $R$ with $R^2=S$, and
--   $$H_W=R(B),\qquad \|Rb\|_H=\|b\|_B\quad\text{for }b\perp\ker R.$$
--   The restriction selects the minimum-norm preimage and includes degenerate covariance operators; the printed formula without this restriction fails when $\ker S\ne0$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 6, Example 2.1: Hilbert covariance square root

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Example 2.1: Hilbert covariance square root, arXiv:0805.3252v1, PDF p.6.
SOURCE CORRECTION: printed ||R b||_H=||b|| is restricted to b perpendicular to ker R; the source proof substitutes c=R b, forcing this minimum-preimage reading. Finite trace is the uniform bound on all finite orthonormal diagonal sums; no injectivity is assumed. -/
theorem hilbert_covariance_squareRoot
{E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (W : Omega → E) (hW : BorelCenteredGaussianElement P W) :
    ∃ S R : E →L[ℝ] E,
      (∀ b : E, S b = ∫ o, (inner ℝ (W o) b) • W o ∂P) ∧
      (∀ x y : E, inner ℝ x (S y) = inner ℝ (S x) y) ∧
      (∀ x : E, 0 ≤ inner ℝ x (S x)) ∧
      (∃ bound : ℝ, 0 ≤ bound ∧ ∀ (n : ℕ) (e : Fin n → E),
        Orthonormal ℝ e → ∑ i, inner ℝ (e i) (S (e i)) ≤ bound) ∧
      (∀ x y : E, inner ℝ x (R y) = inner ℝ (R x) y) ∧
      (∀ x : E, 0 ≤ inner ℝ x (R x)) ∧
      (∀ x : E, R (R x) = S x) ∧
      banachRKHS P W = Set.range R ∧
      ∀ b : E, (∀ c : E, R c = 0 → inner ℝ b c = 0) →
        banachNorm P W (R b) = ‖b‖ := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
