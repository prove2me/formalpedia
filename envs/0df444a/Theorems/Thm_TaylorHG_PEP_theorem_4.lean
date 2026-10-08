-- Prove2me | Theorems.Thm_TaylorHG_PEP_theorem_4
-- name    : TaylorHG.PEP.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:57.171985+00:00
-- url     : https://prove2.me/theorems/349ba217-a36d-4172-8f08-99e9d91bbbe9
-- title:
--   Theorem 4 — exact smooth strongly convex interpolation
-- statement:
--   For finite triples $(x_i,g_i,f_i)$ and $0\leq\mu<L\leq\infty$, interpolation by $\mathcal F_{\mu,L}$ is equivalent to every ordered pair satisfying
--
--   $$f_i-f_j-\langle g_j,x_i-x_j\rangle\geq\frac{\frac1L\|g_i-g_j\|^2+\mu\|x_i-x_j\|^2-\frac{2\mu}{L}\langle g_j-g_i,x_j-x_i\rangle}{2(1-\mu/L)}.$$
--
--   This necessary and sufficient criterion is the paper's bridge from functions to finite data.
--
--   **Formalization Note** The data index is finite, interpolants are real-valued, and $1/\infty=0$.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 10, Theorem 4 and (4)

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

theorem theorem_4 {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable μ L x g fv ↔ ∀ i j, InterpIneq μ L x g fv i j := by sorry

end TaylorHG.PEP
