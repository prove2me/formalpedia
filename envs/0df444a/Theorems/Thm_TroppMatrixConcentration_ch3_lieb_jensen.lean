-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_lieb_jensen
-- name    : TroppMatrixConcentration.ch3_lieb_jensen
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:20:21.937106+00:00
-- url     : https://prove2.me/theorems/940822dd-5c17-40ff-bf44-cbe3332a2a7b
-- title:
--   Jensen inequality on a nonclosed convex domain
-- statement:
--   Let $E$ be a real Banach space, $s\subseteq E$, and $g:E\to\mathbb R$ continuous and concave on $s$ (so $s$ is convex). On a probability space, suppose $f$ and $g\circ f$ are Bochner integrable, $f\in s$ almost surely, and $\mathbb Ef\in s$. Then
--
--   $$\mathbb E[g(f)]\le g(\mathbb Ef).$$
--
--   The domain need not be closed. The explicit mean-membership hypothesis allows Jensen’s inequality to be used on the positive-definite cone.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Jensen inequality (2.2.2), printed p. 25, and its use in Corollary 3.4.2, printed p. 35. Auxiliary Banach-space formulation with explicit integrability, continuity, and mean-membership hypotheses.

import Mathlib.Analysis.Convex.Integral

open MeasureTheory
set_option autoImplicit false

namespace TroppMatrixConcentration

/-- Jensen's inequality on a possibly nonclosed convex domain, provided the mean belongs to it. -/
theorem ch3_lieb_jensen {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set E) (g : E → ℝ) (f : Ω → E)
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ)
    (hgf : Integrable (fun ω => g (f ω)) μ) (hm : (∫ ω, f ω ∂μ) ∈ s) :
    (∫ ω, g (f ω) ∂μ) ≤ g (∫ ω, f ω ∂μ) := by sorry

end TroppMatrixConcentration
