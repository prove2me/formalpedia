-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_process_banach_agreement
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.process_banach_agreement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:37:47.415991+00:00
-- url     : https://prove2.me/theorems/355e1efd-ed0a-4e86-b1e2-ac53683ea8d7
-- title:
--   Theorem 2.1: agreement of process and Banach RKHSs (seed result)
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a complete separable real linear subspace $B\subseteq\ell^\infty(T)$ with its inherited uniform norm. The Banach and stochastic-process RKHSs agree, including their Hilbert inner products, under evaluation as functions on $T$. Moreover
--   $$S\pi_t(s)=K(t,s)=E[W_tW_s].$$
--   The index set is arbitrary and the zero-dimensional case is allowed.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 7, Theorem 2.1: agreement of process and Banach RKHSs (seed result)

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

/-- Theorem 2.1: agreement of process and Banach RKHSs (seed result), arXiv:0805.3252v1, PDF p.7.
The evaluation family and norm equality encode an isometric uniform-function subspace. The boundedness clause guards real suprema; T empty forces B={0}. -/
theorem process_banach_agreement
{T : Type w} (ev : T → B →L[ℝ] ℝ)
    (hbounded : ∀ b : B, BddAbove (Set.range (fun t => |ev t b|)))
    (hnorm : ∀ b : B, ‖b‖ = sSup (Set.range (fun t => |ev t b|)))
    (W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (fun b : B => fun t => ev t b) '' banachRKHS P W =
      processRKHS P (fun t o => ev t (W o)) ∧
    (∀ b ∈ banachRKHS P W, ∀ c ∈ banachRKHS P W,
      banachInner P W b c = processInner P (fun t o => ev t (W o))
        (fun t => ev t b) (fun t => ev t c)) ∧
    ∀ s t : T, ev s (covarianceMap P W (ev t)) =
      processCovariance P (fun t o => ev t (W o)) t s := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
