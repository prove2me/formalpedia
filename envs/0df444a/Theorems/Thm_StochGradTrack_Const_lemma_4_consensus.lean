-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_4_consensus
-- name    : StochGradTrack.Const.lemma_4_consensus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:21.726688+00:00
-- url     : https://prove2.me/theorems/a21f10cd-a6f6-4be9-8aa7-217034289b84
-- title:
--   Lemma 4, (19), p. 420 — ‖x_{k+1} − 1x̄_{k+1}‖² ≤ ((1 + ρ_w²)/2)‖x_k − 1x̄_k‖² + α²((1 + ρ_w²)ρ_w²/(1 − ρ_w²))‖y_k − 1ȳ_k‖²
-- statement:
--   Let $\mathbf W$ satisfy Assumptions 3–4 and run DSGT (4) with constant stepsize $\alpha>0$ from any deterministic $\mathbf x_0$, with any oracle $g_i$ and any noise. Then for every $k\ge0$ and every realization,
--   $$\|\mathbf x_{k+1}-\mathbf 1\bar x_{k+1}\|^2\le\frac{1+\rho_w^2}{2}\|\mathbf x_k-\mathbf 1\bar x_k\|^2+\alpha^2\frac{(1+\rho_w^2)\rho_w^2}{1-\rho_w^2}\|\mathbf y_k-\mathbf 1\bar y_k\|^2 .$$
--
--   This is the second row of (21): the consensus error contracts by $(1+\rho_w^2)/2<1$ per step, driven by the disagreement of the trackers.
--
--   **Formalization Note.** The inequality is pathwise and uses only Assumptions 3–4 (through Lemma 1, which gives $\rho_w<1$); the oracle and noise assumptions are not hypotheses. Norms are Frobenius.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 4 with (19), p. 420

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_4_consensus {n p m : ℕ} {Ω : Type*} (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : Assumption34 W) (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m)
    (x0 : Stack n p) (α : ℝ) (hα : 0 < α) :
    ∀ k ω, consErr (xs (fun _ => α) W g ξ x0 (k + 1) ω) ≤ (1 + rhoW W ^ 2) / 2 * consErr (xs (fun _ => α) W g ξ x0 k ω)
      + α ^ 2 * ((1 + rhoW W ^ 2) * rhoW W ^ 2 / (1 - rhoW W ^ 2)) * consErr (ys (fun _ => α) W g ξ x0 k ω) := by sorry

end StochGradTrack.Const
