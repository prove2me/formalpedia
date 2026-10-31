-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_continuous_process_agreement
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.continuous_process_agreement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:38:25.726825+00:00
-- url     : https://prove2.me/theorems/334fbff3-9471-4a5b-9305-e23a5d2db73a
-- title:
--   Example 2.2: comparison for continuous functions
-- statement:
--   Let $T$ be a compact metric space and $W$ a Borel centered Gaussian random element of $C(T,\mathbb R)$ with the uniform norm. Its Banach and coordinate-process RKHSs agree as functions and have the same inner product:
--   $$H_W^{\mathrm{process}}=\{t\mapsto h(t):h\in H_W^{C(T)}\}.$$
--   This applies in particular to $C[0,1]$ and presupposes the stated Borel random element.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 7, Example 2.2: comparison for continuous functions

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

/-- Example 2.2: comparison for continuous functions, arXiv:0805.3252v1, PDF p.7.
No measurability is inferred merely from a set of continuous paths. Empty compact T is permitted. -/
theorem continuous_process_agreement
{T : Type v} [MetricSpace T] [CompactSpace T]
    (W : Omega → C(T, ℝ)) (hW : BorelCenteredGaussianElement P W) :
    (fun f : C(T, ℝ) => fun t => f t) '' banachRKHS P W =
      processRKHS P (fun t o => W o t) ∧
    ∀ f ∈ banachRKHS P W, ∀ g ∈ banachRKHS P W,
      banachInner P W f g = processInner P (fun t o => W o t)
        (fun t => f t) (fun t => g t) := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
