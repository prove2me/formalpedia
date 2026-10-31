-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_rkhs_weaker_norm_completion
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.rkhs_weaker_norm_completion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:49:02.576566+00:00
-- url     : https://prove2.me/theorems/5b195868-5afa-43f2-8608-ac5388d3a2ba
-- title:
--   Lemma 8.1: changing to a weaker norm
-- statement:
--   Let $B$ be a real separable Banach space, and put a second genuine norm $\|\cdot\|'\le\|\cdot\|$ on its vector space. Let $\widehat B'$ be its completion in that norm, and $j$ the canonical embedding. A Borel centered Gaussian element $W$ has the same RKHS after this embedding, including its Hilbert norm:
--   $$H_{jW}=j(H_W),\qquad\|jh\|_{H_{jW}}=\|h\|_{H_W}.$$
--   No equivalence of the two norms and no completeness of the weaker norm is required.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 18, Lemma 8.1: changing to a weaker norm

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

/-- Lemma 8.1: changing to a weaker norm, arXiv:0805.3252v1, PDF p.18.
A linear type equivalence transports the same underlying vector space to the weaker genuine norm; the final embedding is the canonical completion map, not an arbitrary target isomorphism. -/
theorem rkhs_weaker_norm_completion
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ident : B ≃ₗ[ℝ] E) (hweaker : ∀ b : B, ‖ident b‖ ≤ ‖b‖)
    (W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    banachRKHS P (fun o => (ident (W o) : UniformSpace.Completion E)) =
      (fun b : B => (ident b : UniformSpace.Completion E)) '' banachRKHS P W ∧
    ∀ h ∈ banachRKHS P W,
      banachNorm P (fun o => (ident (W o) : UniformSpace.Completion E))
        (ident h : UniformSpace.Completion E) = banachNorm P W h := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
