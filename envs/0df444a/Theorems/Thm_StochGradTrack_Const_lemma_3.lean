-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_3
-- name    : StochGradTrack.Const.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:21.479364+00:00
-- url     : https://prove2.me/theorems/a46415d8-cd1c-472f-b598-64aced7d772a
-- title:
--   Lemma 3, (17), p. 419 — ‖∇f(x̄) − h(x)‖ ≤ (L/√n)‖x − 1x̄‖
-- statement:
--   Let each $\nabla f_i:\mathbb R^p\to\mathbb R^p$ be $L$-Lipschitz. For every stacked $\mathbf x\in\mathbb R^{n\times p}$ with average $\bar x$, writing $\nabla f(\bar x)=\frac1n\sum_i\nabla f_i(\bar x)$ and $h(\mathbf x)=\frac1n\sum_i\nabla f_i(x_i)$,
--   $$\|\nabla f(\bar x)-h(\mathbf x)\|\le\frac{L}{\sqrt n}\,\|\mathbf x-\mathbf 1\bar x\| .$$
--
--   The page states this for the iterates $\mathbf x_k$; it bounds how far the averaged local gradients are from the true gradient at the average, in terms of the consensus error.
--
--   **Formalization Note.** The page says "for all $k\ge0$" about $\mathbf x_k$; the claim holds for every stacked $\mathbf x$ and is stated so. Only the Lipschitz half of Assumption 2 is used. $\|\mathbf x-\mathbf 1\bar x\|$ is the Frobenius norm.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 3 with (17), p. 419

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_3 {n p : ℕ} (gradf : Fin n → E p → E p) (L : ℝ)
    (hL : ∀ i (x x' : E p), ‖gradf i x - gradf i x'‖ ≤ L * ‖x - x'‖) (x : Stack n p) :
    ‖gradAvg gradf (avg x) - hAvg gradf x‖ ≤ L / Real.sqrt n * Real.sqrt (consErr x) := by sorry

end StochGradTrack.Const
