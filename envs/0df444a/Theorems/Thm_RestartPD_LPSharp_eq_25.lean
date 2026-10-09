-- Prove2me | Theorems.Thm_RestartPD_LPSharp_eq_25
-- name    : RestartPD.LPSharp.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:02.546965+00:00
-- url     : https://prove2.me/theorems/5b160b1b-8ffc-451e-a345-b37ca330f859
-- title:
--   (25), proof of Lemma 4, p. 14 — ρ_r(z) ≥ (1/R)(c⊤x − b⊤y)⁺ for z ∈ W_R(0) and 0 < r ≤ R
-- statement:
--   Let $A$, $b$, $c$, $L$ and $Z=\{x\ge0\}\times\mathbb R^m$ be as in the LP setup (19), with the Euclidean norm on $\mathbb R^{n+m}$. Let $R>0$, let $z=(x,y)\in W_R(0)$, i.e. $z\in Z$ and $\|z\|\le R$, and let $0<r\le R$. Then
--   $$\rho_r(z)\ \ge\ \frac1R\,\big(c^\top x-b^\top y\big)^+.$$
--
--   This is the half of Lemma 4 that controls the duality gap $c^\top x-b^\top y$ by the normalized duality gap on a bounded region.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 14, (25) in the proof of Lemma 4

import Mathlib
import Definitions.Def_RestartPD_LPSharp_PrimalDual
import Definitions.Def_RestartPD_LPSharp_LP
open scoped InnerProductSpace Matrix

namespace RestartPD.LPSharp

theorem eq_25 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) (z : PDSpace n m)
    (hz : z ∈ Wball lpX Set.univ R 0) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ((max (⟪c, z.1⟫_ℝ - ⟪b, z.2⟫_ℝ) 0 / R : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by sorry

end RestartPD.LPSharp
