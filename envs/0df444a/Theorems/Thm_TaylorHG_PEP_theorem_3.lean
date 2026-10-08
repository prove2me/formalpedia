-- Prove2me | Theorems.Thm_TaylorHG_PEP_theorem_3
-- name    : TaylorHG.PEP.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:41.69712+00:00
-- url     : https://prove2.me/theorems/3a1fc2a6-d099-4c57-a048-a23b70ff52b0
-- title:
--   Theorem 3 — subtracting minimal curvature
-- statement:
--   Let $f$ be convex and let $0\leq\mu<L\leq\infty$. Then
--
--   $$f\in\mathcal F_{\mu,L}\quad\Longleftrightarrow\quad f-\frac\mu2\|\cdot\|^2\in\mathcal F_{0,L-\mu}.$$
--
--   This identifies the curvature subtraction used to reduce general interpolation to smooth convex interpolation.
--
--   **Formalization Note** The function is real-valued; $\infty-\mu=\infty$ follows the paper's convention.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 8, Theorem 3

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

theorem theorem_3 {d : ℕ} (μ : NNReal) (L : ENNReal)
    (hμL : (μ : ENNReal) < L) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : FClass 0 ⊤ f) :
    FClass μ L f ↔
      FClass 0 (L - (μ : ENNReal))
        (fun x => f x - (μ : ℝ) / 2 * ‖x‖ ^ 2) := by sorry

end TaylorHG.PEP
