-- Prove2me | Theorems.Thm_SubsetShrink_L1_h_display
-- name    : SubsetShrink.L1.h_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:47.311668+00:00
-- url     : https://prove2.me/theorems/aaf6b8df-7a19-4528-a345-8aaba10558f2
-- title:
--   p. 43 — the H-event correlation bound
-- statement:
--   For coefficient vectors $\hat\beta_1$ and $\beta$, the correlation with the noise is at most twice the maximum absolute coordinate of $X^\top\epsilon$ times their combined $\ell_1$ norms. At the first tuning value in Theorem 3(A), on $\mathcal H$ this becomes
--
--   $$2\epsilon^\top X(\hat\beta_1-\beta)\le2\|X^\top\epsilon\|_\infty(\|\beta\|_1+\|\hat\beta_1\|_1)\le\lambda(\|\hat\beta_1\|_1+\|\beta\|_1).$$
--
--   It provides the noise control in the exact slow-rate inequality.
--
--   **Formalization Note** The tuning value uses the same $\delta_0$ as $\mathcal H$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 43, first display of proof B.6

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- The first display of B.6, p. 43: the norm inequality and its SubsetShrink.Events.H-event bound.
The paper's lambda is tied to the same `δ0` as SubsetShrink.Events.H. -/
theorem h_display {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (ε : Fin n → ℝ) (βhat β : Fin p → ℝ)
    (σ δ0 lam : ℝ) (hσ : 0 < σ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hp : 1 ≤ p)
    (hlam : lam = 2 * σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) +
      2 * σ * Real.sqrt (2 * Real.log (1 / δ0))) :
    2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
      2 * lInf (X.transpose.mulVec ε) * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) ∧
    (ε ∈ SubsetShrink.Events.H X σ δ0 →
      2 * lInf (X.transpose.mulVec ε) * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) ≤
        lam * (SubsetShrink.Events.l1 βhat + SubsetShrink.Events.l1 β)) := by sorry

end SubsetShrink.L1
