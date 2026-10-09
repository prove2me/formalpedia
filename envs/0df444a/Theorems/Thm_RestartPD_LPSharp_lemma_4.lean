-- Prove2me | Theorems.Thm_RestartPD_LPSharp_lemma_4
-- name    : RestartPD.LPSharp.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:07.290338+00:00
-- url     : https://prove2.me/theorems/716d6546-00ca-4611-a676-acfb6368d140
-- title:
--   Lemma 4, p. 14 — ‖(h − Kz)⁺‖ ≤ ρ_r(z)√(1 + R²) for z ∈ W_R(0), r ∈ (0, R]
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $L(x,y)=c^\top x+y^\top b-y^\top Ax$ be the Lagrangian (19) on $Z=\{x\ge0\}\times\mathbb R^m$, equipped with the Euclidean norm, and let $K,h$ be the KKT data (20). Suppose (19) has a saddle point. Then for all $R\in(0,\infty)$, $r\in(0,R]$ and $z\in W_R(0)$,
--   $$\|(h-Kz)^+\|\ \le\ \rho_r(z)\,\sqrt{1+R^2}.$$
--
--   The KKT residual, a standard stopping criterion for LP, is thus bounded by the normalized duality gap; combined with Hoffman's bound this gives sharpness of LP (Lemma 5).
--
--   **Formalization Note** The inequality is stated in the extended reals, with $\sqrt{1+R^2}>0$ coerced. The hypothesis that a solution exists is kept as on the page, although it is not needed for the inequality.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 14, Lemma 4

import Mathlib
import Definitions.Def_RestartPD_LPSharp_PrimalDual
import Definitions.Def_RestartPD_LPSharp_LP
open scoped InnerProductSpace Matrix

namespace RestartPD.LPSharp

theorem lemma_4 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (hsol : (Zstar (lpL A b c) lpX Set.univ).Nonempty)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) (z : PDSpace n m)
    (hz : z ∈ Wball lpX Set.univ R 0) :
    ((kktRes A b c z : ℝ) : EReal) ≤
      rho (lpL A b c) lpX Set.univ r z * ((Real.sqrt (1 + R ^ 2) : ℝ) : EReal) := by sorry

end RestartPD.LPSharp
