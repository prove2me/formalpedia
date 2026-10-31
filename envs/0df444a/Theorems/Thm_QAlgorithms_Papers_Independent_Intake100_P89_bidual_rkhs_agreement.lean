-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_bidual_rkhs_agreement
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.bidual_rkhs_agreement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:38:55.721446+00:00
-- url     : https://prove2.me/theorems/9359d0ef-ad73-41d6-afde-a02ffe214f21
-- title:
--   §2.3, unnumbered comparison via the canonical bidual embedding
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space $B$. Its evaluation process $W^{**}_\ell=\ell(W)$ has a process RKHS equal, as a set and isometrically, to the Banach RKHS under the canonical map $b\mapsto(\ell\mapsto\ell(b))$:
--   $$H_{W^{**}}=\{\ell\mapsto\ell(h):h\in H_W\}.$$
--   The covariance section at $\ell$ is the same canonical image of $S\ell$. Neither reflexivity nor norm separability of $B^*$ is required.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 7, §2.3, unnumbered comparison via the canonical bidual embedding

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

/-- §2.3, unnumbered comparison via the canonical bidual embedding, arXiv:0805.3252v1, PDF p.7.
The bidual embedding is actual dual evaluation, not a chosen isomorphism. -/
theorem bidual_rkhs_agreement
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (fun b : B => fun l : B →L[ℝ] ℝ => l b) '' banachRKHS P W =
      processRKHS P (fun l : B →L[ℝ] ℝ => fun o => l (W o)) ∧
    (∀ b ∈ banachRKHS P W, ∀ c ∈ banachRKHS P W,
      banachInner P W b c = processInner P
        (fun l : B →L[ℝ] ℝ => fun o => l (W o))
        (fun l => l b) (fun l => l c)) ∧
    ∀ l m : B →L[ℝ] ℝ, m (covarianceMap P W l) =
      processCovariance P (fun l : B →L[ℝ] ℝ => fun o => l (W o)) l m := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
