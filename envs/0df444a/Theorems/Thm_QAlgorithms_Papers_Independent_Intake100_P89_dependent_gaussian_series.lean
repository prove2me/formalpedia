-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_dependent_gaussian_series
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.dependent_gaussian_series
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:42:22.204997+00:00
-- url     : https://prove2.me/theorems/50d3d230-f059-422d-be26-97f03e811fe9
-- title:
--   §4, unnumbered Gaussian series without independence of directions
-- statement:
--   Retain the convergent Banach Gaussian series $W=\sum_iZ_ih_i$, with iid standard normal coefficients, but drop injectivity of deterministic synthesis. Let $C\subseteq\ell^2$ be the closed span of the dual coefficient sequences $(\ell(h_i))_i$. Every $\ell^2$ series converges and
--   $$H_W=\left\{\sum_iw_ih_i:w\in C\right\}=\left\{\sum_iw_ih_i:w\in\ell^2\right\}.$$
--   Synthesis is one-to-one on $C$, and its RKHS norm is $\|w\|_2$ there. For arbitrary coefficients it is the norm of their orthogonal projection onto $C$. This handles nonunique directions without assigning the wrong norm.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 12, §4, unnumbered Gaussian series without independence of directions

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

/-- §4, unnumbered Gaussian series without independence of directions, arXiv:0805.3252v1, PDF p.12.
The coefficient projection is characterized by orthogonality, rather than supplied as an arbitrary map. Duplicate directions h1=h2 give minimum energy (a+b)^2/2. -/
theorem dependent_gaussian_series
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (h : ℕ → B) (Z : ℕ → Omega → ℝ) (hZ : StandardNormals P Z)
    (W : Omega → B) (hW : @Measurable Omega B _ (borel B) W)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => ∑ i ∈ Finset.range n, Z i o • h i)
      atTop (𝓝 (W o))) :
    BorelCenteredGaussianElement P W ∧
    (∀ l : B →L[ℝ] ℝ, Memℓp (fun i => l (h i)) 2) ∧
    (∀ w : SeqL2, Summable (fun i => w i • h i)) ∧
    banachRKHS P W = Set.range (fun w : identifiableCoefficientSubspace h => series h (w : SeqL2)) ∧
    Function.Injective (fun w : identifiableCoefficientSubspace h => series h (w : SeqL2)) ∧
    (∀ w : identifiableCoefficientSubspace h, banachNorm P W (series h (w : SeqL2)) = ‖w‖) ∧
    ∀ w : SeqL2, ∃ v : identifiableCoefficientSubspace h,
      (∀ z : identifiableCoefficientSubspace h, inner ℝ (w - (v : SeqL2)) (z : SeqL2) = 0) ∧
      series h w = series h (v : SeqL2) ∧ banachNorm P W (series h w) = ‖v‖ := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
