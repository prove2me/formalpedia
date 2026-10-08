-- Prove2me | Theorems.Thm_TaylorHG_PEP_lemma_2
-- name    : TaylorHG.PEP.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:57.207074+00:00
-- url     : https://prove2.me/theorems/b9d44a6e-5cef-4b02-9b73-70b5da17b228
-- title:
--   Lemma 2 — conjugate interpolation data
-- statement:
--   For finite data and $0<L\leq\infty$, $\mathcal F_{0,L}$-interpolability of $(x_i,g_i,f_i)$ is equivalent to $\mathcal F_{1/L,\infty}$-interpolability of
--
--   $$\left(g_i,\ x_i,\ \langle x_i,g_i\rangle-f_i\right)_{i\in I}.$$
--
--   The equivalence exchanges points and subgradients, as in conjugacy.
--
--   **Formalization Note** The statement uses finite data and real-valued interpolating functions; $1/\infty=0$.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 9, Lemma 2

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

theorem lemma_2 {d : ℕ} {ι : Type*} [Fintype ι]
    (L : ENNReal) (hL : 0 < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable 0 L x g fv ↔
      Interpolable (L⁻¹).toNNReal ⊤ g x
        (fun i => inner ℝ (x i) (g i) - fv i) := by sorry

end TaylorHG.PEP
