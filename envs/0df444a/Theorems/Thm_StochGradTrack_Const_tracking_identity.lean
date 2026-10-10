-- Prove2me | Theorems.Thm_StochGradTrack_Const_tracking_identity
-- name    : StochGradTrack.Const.tracking_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:15.113162+00:00
-- url     : https://prove2.me/theorems/5922ca41-6047-44ed-826a-fb96b1cc63cd
-- title:
--   (6), p. 415 — the average tracker equals the average stochastic gradient: ȳ_k = (1/n) Σᵢ gᵢ(x_{i,k}, ξ_{i,k})
-- statement:
--   Let $\mathbf W\in\mathbb R^{n\times n}$ have unit column sums, $\mathbf 1^\top\mathbf W=\mathbf 1^\top$, and run DSGT (4) with constant stepsize $\alpha$ from any deterministic $\mathbf x_0$, with $y_{i,0}=g_i(x_{i,0},\xi_{i,0})$. Then for every $k\ge0$ and every realization of the noise,
--   $$\bar y_k=\frac1n\mathbf 1^\top G(\mathbf x_k,\boldsymbol\xi_k)=\frac1n\sum_{i=1}^n g_i(x_{i,k},\xi_{i,k}).$$
--
--   This is why $y_{i,k}$ is called a tracker: the network average of the trackers equals the average of the current stochastic gradients, so once the trackers agree each of them approximately follows the averaged gradient.
--
--   **Formalization Note.** The identity is pathwise and uses only $\mathbf 1^\top\mathbf W=\mathbf 1^\top$ from Assumptions 1–4, which are therefore not hypotheses here. The page writes $y_{i,0}=g(x_{i,0},\xi_{i,0})$ without the index $i$; the recursion (4) and this statement use $g_i$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), (6), p. 415

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem tracking_identity {n p m : ℕ} {Ω : Type*} (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (x0 : Stack n p)
    (hcol : ∀ j, ∑ i, W i j = 1) :
    ∀ k ω, avg (ys (fun _ => α) W g ξ x0 k ω) = (n : ℝ)⁻¹ • ∑ i, g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω) := by sorry

end StochGradTrack.Const
