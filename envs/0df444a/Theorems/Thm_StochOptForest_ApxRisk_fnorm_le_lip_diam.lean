-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_fnorm_le_lip_diam
-- name    : StochOptForest.ApxRisk.fnorm_le_lip_diam
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:59.578216+00:00
-- url     : https://prove2.me/theorems/16c74703-4228-482a-8812-1b7861fe4921
-- title:
--   Proof of Theorem 2, p. 81 — ‖f_j − f₀‖_F ≤ L·D₀ under the Lipschitz condition
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^p$ and $\bar c$ a regression cost that is twice continuously differentiable in $z$ and $x$-Lipschitz with constant $L$ (in $\bar c$, $\nabla_z\bar c$ and $\nabla^2_z\bar c$, uniformly in $z$). Let $R_j\subseteq R_0\subseteq\mathbb R^p$ be measurable, $R_0$ bounded with diameter $\mathcal D_0=\sup_{x,x'\in R_0}\|x-x'\|_2$, and $\mu(R_j)>0$. Then for every $z\in\mathbb R^d$
--   $$|f_j(z)-f_0(z)|\le L\mathcal D_0,\qquad \|\nabla f_j(z)-\nabla f_0(z)\|_2\le L\mathcal D_0,\qquad \|\nabla^2 f_j(z)-\nabla^2 f_0(z)\|\le L\mathcal D_0,$$
--   that is, $\|f_j-f_0\|_{\mathcal F}\le L\mathcal D_0$.
--
--   This bound is the input that converts the $o(\|f_j-f_0\|^2_{\mathcal F})$ error of Theorem 9 into the $o(\mathcal D_0^2)$ error of Theorem 2.
--
--   **Formalization Note** The paper writes $\|f_j-f_0\|_{\mathcal F}=O(\mathcal D_0^2)$; the correct order is $O(\mathcal D_0)$ (for $\bar c(x,z)=(z-x)^2/2$ the gradients differ by the difference of the region means of $X$), and $O(\mathcal D_0)$ is what the conclusion of Theorem 2 needs. Condition 4 of Theorem 2 is read as the $x$-Lipschitz bound on $\bar c$ and its first two $z$-derivatives, which is how the proof uses it. The Hessian difference is measured in operator norm.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 81, Proof for Theorem 2 (and p. 65, last paragraph of §D.4)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

open MeasureTheory

theorem fnorm_le_lip_diam {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (hC2 : ∀ x, ContDiff ℝ 2 (cbar x))
    (hLip : XLipschitz cbar L) (R0 Rj : Set (Xp p)) (hR0 : MeasurableSet R0)
    (hRj : MeasurableSet Rj) (hsub : Rj ⊆ R0) (hR0b : Bornology.IsBounded R0)
    (hpos : 0 < μ Rj) :
    FNormLE (fun z => regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) (L * Metric.diam R0) := by sorry

end StochOptForest.ApxRisk
