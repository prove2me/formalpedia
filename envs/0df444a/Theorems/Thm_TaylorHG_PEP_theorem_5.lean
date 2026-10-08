-- Prove2me | Theorems.Thm_TaylorHG_PEP_theorem_5
-- name    : TaylorHG.PEP.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:52.024842+00:00
-- url     : https://prove2.me/theorems/a8d1353f-2522-4769-bc44-e9faf8d2f2cc
-- title:
--   Theorem 5 — exact SDP performance estimation
-- statement:
--   Fix $0\leq\mu<L<\infty$, a fixed-step method $H$ taking $N$ steps, a radius $R\geq0$, and a criterion with coefficients $b\in\mathbb R^{N+1}$ and symmetric $C\in\mathbb S^{N+2}$. In every dimension $d\geq N+2$, the worst performance over functions in $\mathcal F_{\mu,L}(\mathbb R^d)$ equals the optimal value of the semidefinite program:
--
--   $$w^{(d)}_{\mu,L}(R,H,N,P_{b,C})=w^{\mathrm{sdp}}_{\mu,L}(R,H,N,b,C).$$
--
--   The result makes the finite SDP an exact value computation for this class of methods and criteria.
--
--   **Formalization Note** Both values are extended-real suprema. The function-level criterion is translated around an explicit minimizer. The paper's display allows $L=\infty$, but its $A_{ij}$ coefficients are undefined there; Remark 4 restricts the subsequent SDP analysis to finite $L$. A nonnegative radius is implicit in a norm bound and is required for the squared-radius SDP constraint.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 14, Theorem 5 and (sdp-PEP)

import Mathlib
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHG.PEP

theorem theorem_5 {N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (R : ℝ) (hR : 0 ≤ R) (H : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (d : ℕ) (hd : N + 2 ≤ d) :
    worstCase d μ L R H b C = sdpValue μ L R H b C := by sorry

end TaylorHG.PEP
