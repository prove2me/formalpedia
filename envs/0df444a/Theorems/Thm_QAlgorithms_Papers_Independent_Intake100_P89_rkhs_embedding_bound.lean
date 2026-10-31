-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_rkhs_embedding_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.rkhs_embedding_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:33:47.242237+00:00
-- url     : https://prove2.me/theorems/8335763f-34be-4709-8cf2-44b0dc724018
-- title:
--   §2.2, embedding bound (2.4)–(2.5)
-- statement:
--   Let $W$ be a Borel centered Gaussian random element of a real separable Banach space $B$, with covariance RKHS $H$. Define $\sigma(W)^2=\sup_{\|\ell\|\le1}E[\ell(W)^2]$. The canonical embedding satisfies
--   $$\|h\|_B\le\sigma(W)\|h\|_H\quad(h\in H),\qquad H_1\subseteq\sigma(W)B_1.$$
--   The closed-dual-ball convention includes $B=\{0\}$ and agrees with the printed sphere formula otherwise.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 4, §2.2, embedding bound (2.4)–(2.5)

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

/-- §2.2, embedding bound (2.4)–(2.5), arXiv:0805.3252v1, PDF p.4.
The H norm is the first-chaos completion norm. Finiteness of Gaussian norm moments is not assumed. -/
theorem rkhs_embedding_bound
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (∀ h ∈ banachRKHS P W, ‖h‖ ≤ weakSigma P W * banachNorm P W h) ∧
    (∀ h ∈ rkhsUnitBall P W, ‖h‖ ≤ weakSigma P W) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
