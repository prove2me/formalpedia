-- Prove2me | Theorems.Thm_QCQPTightness_SOCP_schur_diag_ge
-- name    : QCQPTightness.SOCP.schur_diag_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:56.218466+00:00
-- url     : https://prove2.me/theorems/e66a5ba0-f1f3-48e7-b299-0009d007e5d3
-- title:
--   App. A, proof of Proposition 1, p. 34 — if [[1, xᵀ], [x, X]] ⪰ 0 then X ⪰ xxᵀ and X_jj ≥ x_j²
-- statement:
--   Let $x \in \mathbb{R}^N$ and $X \in \mathbb{R}^{N \times N}$. If the lifted matrix
--
--   $$
--   Y = \begin{pmatrix} 1 & x^\top \\ x & X \end{pmatrix} \succeq 0,
--   $$
--
--   then $X - x x^\top \succeq 0$; in particular $X_{jj} \ge x_j^2$ for every $j \in [\![N]\!]$.
--
--   This is the Schur-complement step in the proof that $\mathcal{D}_{\mathrm{SDP}} \subseteq \mathcal{D}_{\mathrm{SOCP}}$: the diagonal of an SDP-feasible $X$ is an SOCP-feasible $y$.
-- source:
--   arXiv:1911.09195v3, App. A, proof of Proposition 1, p. 34, Schur complement step

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP

namespace QCQPTightness.SOCP

open Matrix

/-- App. A, proof of Proposition 1, p. 34, Schur complement step: if
`Y = [[1, xᵀ], [x, X]] ⪰ 0` then `X ⪰ xxᵀ`, and in particular `X_{jj} ≥ x_j²` for every `j`. -/
theorem schur_diag_ge {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hY : (QCQPTightness.ConvHull.liftY x X).PosSemidef) :
    (X - Matrix.vecMulVec x x).PosSemidef ∧ ∀ j, x j ^ 2 ≤ X j j := by sorry

end QCQPTightness.SOCP
