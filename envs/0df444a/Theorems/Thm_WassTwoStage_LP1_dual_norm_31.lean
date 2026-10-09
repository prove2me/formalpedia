-- Prove2me | Theorems.Thm_WassTwoStage_LP1_dual_norm_31
-- name    : WassTwoStage.LP1.dual_norm_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:55:35.034636+00:00
-- url     : https://prove2.me/theorems/88235e25-19d3-4fd5-83d0-27a20d0a8c9b
-- title:
--   Dual norm of (31): $\|z\|_* = \max_k \max\{z_k/w_+, -z_k/w_-\}$
-- statement:
--   Let $K\ge 1$ and $w_+, w_->0$, and let $\|\xi\| = \sum_{k\in[K]}\max\{w_+\xi_k, -w_-\xi_k\}$ be the gauge (31). Its dual norm $\|z\|_* = \sup\{z^\top\xi : \|\xi\|\le 1\}$ is given, for every $z\in\mathbb R^K$, by
--
--   $$\|z\|_* = \max_{k\in[K]}\Big[\max\Big\{\frac{z_k}{w_+},\, -\frac{z_k}{w_-}\Big\}\Big].$$
--
--   This explicit formula turns the semi-infinite constraint of problem (33) into the $2K$ families of linear constraints of the linear program (32).
--
--   **Formalization Note** The dual norm is the extended-real supremum over the unit ball of the gauge; the identity says in particular that it is finite. $K\ge 1$ is needed for the maximum over $[K]$ to be defined.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, §4.1, proof of Theorem 6, p. 23 (display after (33))

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge

open Matrix

namespace WassTwoStage.LP1

/-- The dual norm of (31), Hanasusanto–Kuhn, arXiv:1609.07505v3, §4.1, p. 23: for `K ≥ 1` and
positive `w₊, w₋`, the polar of the gauge `‖ξ‖ = Σ_k max{w₊ξ_k, −w₋ξ_k}` is
`‖z‖_* = max_{k ∈ [K]} max{z_k / w₊, −z_k / w₋}`. -/
theorem dual_norm_31 {K : ℕ} (hK : 0 < K) (wp wm : ℝ) (hwp : 0 < wp) (hwm : 0 < wm)
    (z : Fin K → ℝ) :
    dualGauge wp wm z =
      ((Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩)
        (fun k => max (z k / wp) (-z k / wm)) : ℝ) : EReal) := by sorry

end WassTwoStage.LP1
