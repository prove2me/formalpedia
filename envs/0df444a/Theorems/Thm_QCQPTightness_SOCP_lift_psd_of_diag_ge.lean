-- Prove2me | Theorems.Thm_QCQPTightness_SOCP_lift_psd_of_diag_ge
-- name    : QCQPTightness.SOCP.lift_psd_of_diag_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:42.798503+00:00
-- url     : https://prove2.me/theorems/98316488-e677-4077-a7b0-0566a2e05699
-- title:
--   App. A, proof of Proposition 1, p. 34 — if y_j ≥ x_j², the matrix X with diagonal y and off-diagonal x_jx_k gives [[1, xᵀ], [x, X]] ⪰ 0
-- statement:
--   Let $x, y \in \mathbb{R}^N$ with $y_j \ge x_j^2$ for all $j \in [\![N]\!]$. Define $X \in \mathbb{S}^N$ by $X_{jj} = y_j$ and $X_{jk} = x_j x_k$ for $j \ne k$. Then
--
--   $$
--   \begin{pmatrix} 1 & x^\top \\ x & X \end{pmatrix} \succeq 0.
--   $$
--
--   This is the construction in the proof that $\mathcal{D}_{\mathrm{SOCP}} \subseteq \mathcal{D}_{\mathrm{SDP}}$: an SOCP-feasible $y$ lifts to an SDP-feasible $X$ with the same diagonal.
-- source:
--   arXiv:1911.09195v3, App. A, proof of Proposition 1, p. 34

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP

namespace QCQPTightness.SOCP

open Matrix

/-- App. A, proof of Proposition 1, p. 34: if `y_j ≥ x_j²` for every `j`, the matrix `X` with
`X_{jj} = y_j` and `X_{jk} = x_j x_k` (`j ≠ k`) gives `[[1, xᵀ], [x, X]] ⪰ 0`. -/
theorem lift_psd_of_diag_ge {N : ℕ} (x y : Fin N → ℝ) (hxy : ∀ j, x j ^ 2 ≤ y j) :
    (QCQPTightness.ConvHull.liftY x (Matrix.of fun j k => if j = k then y j else x j * x k)).PosSemidef := by sorry

end QCQPTightness.SOCP
