-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_rkhs_injective_linear_map
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.rkhs_injective_linear_map
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:48:23.031218+00:00
-- url     : https://prove2.me/theorems/89137347-07c6-4758-911f-391433ba8985
-- title:
--   Lemma 7.1: RKHS under an injective continuous linear map
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space $B$, and let $T:B\to E$ be a continuous injective real linear map into a Banach space $E$. Then $TW$ is centered Gaussian and
--   $$H_{TW}=T(H_W),\qquad\|Th\|_{H_{TW}}=\|h\|_{H_W}.$$
--   The target need not be globally separable; the law is carried by the separable closed span of the image. This describes equality after the actual map $T$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 17, Lemma 7.1: RKHS under an injective continuous linear map

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

/-- Lemma 7.1: RKHS under an injective continuous linear map, arXiv:0805.3252v1, PDF p.17.
No target separability, reflexivity, or dual separability is added; injectivity is retained. -/
theorem rkhs_injective_linear_map
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : B →L[ℝ] E) (hT : Function.Injective T)
    (W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    BorelCenteredGaussianElement P (fun o => T (W o)) ∧
    banachRKHS P (fun o => T (W o)) = T '' banachRKHS P W ∧
    ∀ h ∈ banachRKHS P W,
      banachNorm P (fun o => T (W o)) (T h) = banachNorm P W h := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
