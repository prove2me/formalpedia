-- Prove2me | Theorems.Thm_RestartPD_LPSharp_eq_22
-- name    : RestartPD.LPSharp.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:23.444778+00:00
-- url     : https://prove2.me/theorems/85dd6aa7-abff-4428-929a-06c8ff6b97da
-- title:
--   (22), proof of Lemma 4, p. 14 — ρ_r(z) ≥ ‖v‖ with v = ((−c + A⊤y)⁺, b − Ax)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and consider the LP Lagrangian $L(x,y)=c^\top x+y^\top b-y^\top Ax$ on $Z=\{x\ge0\}\times\mathbb R^m$, with the Euclidean norm on $\mathbb R^{n+m}$. For $z=(x,y)\in Z$ set
--   $$v=\big((-c+A^\top y)^+,\ b-Ax\big).$$
--   Then for every $r>0$ the normalized duality gap satisfies
--   $$\rho_r(z)\ \ge\ \|v\|.$$
--
--   This is the half of Lemma 4 that controls primal infeasibility $\|b-Ax\|$ and dual infeasibility $\|(A^\top y-c)^+\|$ by the normalized duality gap, uniformly in the radius $r$.
--
--   **Formalization Note** The page's assumption that (19) has a solution and the radius $R$ are not needed here and are omitted. When $v=0$ the claim reads $\rho_r(z)\ge0$.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 14, (22) in the proof of Lemma 4

import Mathlib
import Definitions.Def_RestartPD_LPSharp_PrimalDual
import Definitions.Def_RestartPD_LPSharp_LP
open scoped InnerProductSpace Matrix

namespace RestartPD.LPSharp

theorem eq_22 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z ∈ (lpX : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.univ)
    (r : ℝ) (hr : 0 < r) :
    ((eucl n m (vvec A b c z) : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by sorry

end RestartPD.LPSharp
