-- Prove2me | Theorems.Thm_TaylorHG_PEP_interp_constraint_trace
-- name    : TaylorHG.PEP.interp_constraint_trace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:53.868731+00:00
-- url     : https://prove2.me/theorems/50fba45f-21b3-4b40-8c58-6a465e933646
-- title:
--   Section 3.3 — trace form of interpolation constraints
-- statement:
--   Let $G$ be the Gram matrix of arbitrary columns $[g_0,\ldots,g_N,x_0]$, with $x_i$ and $g_i$ represented by $h_i$ and $u_i$. For finite $L>\mu$, each ordered-pair interpolation inequality (4) is equivalent to
--
--   $$f_j-f_i+\operatorname{Tr}(GA_{ij})\leq0.$$
--
--   Also $\operatorname{Tr}(GA_R)=\|x_0\|^2$, and the represented iterates satisfy the fixed-step recurrence. These identities connect the interpolation criterion to SDP constraints.
--
--   **Formalization Note** The columns are arbitrary Euclidean vectors; the star point, gradient and value are zero.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 13, §3.3, rewriting of (4)

import Mathlib
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHG.PEP

theorem interp_constraint_trace {d N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (H : Matrix (Fin N) (Fin N) ℝ)
    (col : Fin (N + 2) → EuclideanSpace ℝ (Fin d))
    (fv : Fin (N + 1) → ℝ) :
    (∀ i j : Option (Fin (N + 1)),
      InterpIneq μ (L : ENNReal) (pointOf H col) (gradOf col) (fext fv) i j ↔
        fext fv j - fext fv i + (gramOf col * Amat μ L H i j).trace ≤ 0) ∧
    (gramOf col * ARmat N).trace = ‖col (Fin.last (N + 1))‖ ^ 2 ∧
    (∀ i : Fin (N + 1),
      pointOf H col (some i) = col (Fin.last (N + 1)) -
        ∑ k : Fin (N + 1), hcoef H i k • col (Fin.castSucc k)) := by sorry

end TaylorHG.PEP
