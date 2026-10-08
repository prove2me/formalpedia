-- Prove2me | Theorems.Thm_TaylorHG_PEP_lemma_1
-- name    : TaylorHG.PEP.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:54.175986+00:00
-- url     : https://prove2.me/theorems/90cdf0f4-673d-4e1b-a7f0-a167f32e05f5
-- title:
--   Lemma 1 — curvature shift of interpolation data
-- statement:
--   For finite data $(x_i,g_i,f_i)$ and $0\leq\mu<L\leq\infty$, the data are $\mathcal F_{\mu,L}$-interpolable if and only if the transformed data
--
--   $$\left(x_i,\ g_i-\mu x_i,\ f_i-\frac\mu2\|x_i\|^2\right)_{i\in I}$$
--
--   are $\mathcal F_{0,L-\mu}$-interpolable. The lemma transfers interpolation between the two function classes.
--
--   **Formalization Note** The index type is finite and the interpolating functions are real-valued.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 9, Lemma 1

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

theorem lemma_1 {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable μ L x g fv ↔
      Interpolable 0 (L - (μ : ENNReal)) x
        (fun i => g i - (μ : ℝ) • x i)
        (fun i => fv i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) := by sorry

end TaylorHG.PEP
