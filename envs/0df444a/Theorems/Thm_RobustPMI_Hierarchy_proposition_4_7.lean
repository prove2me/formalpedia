-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_proposition_4_7
-- name    : RobustPMI.Hierarchy.proposition_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:03.148893+00:00
-- url     : https://prove2.me/theorems/251619a9-5bc8-4941-933f-c5ed90295b53
-- title:
--   Proposition 4.7, p. 20 — Jensen for PSD-SOS-convex matrices: 𝓗_s(Q) ⪰ Q(s_e)
-- statement:
--   This is a Jensen inequality for PSD-SOS-convex polynomial matrices.
--
--   Let $Q(y)\in\mathbb S[y]^m$ be a symmetric polynomial matrix in $y=(y_1,\dots,y_\ell)$ that is PSD-SOS-convex, and let $d=\lceil\deg(Q)/2\rceil$. Let $s=(s_\alpha)_{\alpha\in\mathbb N^\ell_{2d}}$ be a real sequence with $s_0=1$ and moment matrix $M_d(s)\succeq0$. Write $\mathscr H_s(Q)$ for the matrix with entries $\mathscr H_s(Q_{ij})=\sum_\alpha (Q_{ij})_\alpha s_\alpha$, and $s_e=(s_{e_1},\dots,s_{e_\ell})$ for the first-order moments. Then
--   $$\mathscr H_s(Q)\succeq Q(s_e).$$
--
--   When $s$ is the moment sequence of a probability measure this is Jensen's inequality for the matrix-concave map $-Q$; the point is that only the positive semidefiniteness of a truncated moment matrix is required. It is what turns a solution of the dual relaxation into a feasible point of (RPMIO).
--
--   **Formalization Note** The scalar moment matrix $M_d(s)$ is the $m=1$ case of the matrix moment matrix. The sequence $s$ is a total function on all exponents; only $|\alpha|\le 2d$ is read.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 20, Proposition 4.7

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open MvPolynomial

/-- Proposition 4.7 (p. 20): if `Q(y) ∈ 𝕊[y]^m` is PSD-SOS-convex and `s` satisfies `s_0 = 1` and
`M_{⌈deg(Q)/2⌉}(s) ⪰ 0`, then `𝓗_s(Q) ⪰ Q(s_e)`. -/
theorem proposition_4_7 {ℓ m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ))
    (hQ : Q.IsSymm) (hconv : IsPSDSOSConvex Q) (v : (Fin ℓ →₀ ℕ) → ℝ) (hv0 : v 0 = 1)
    (hM : (momentMat ((degMat Q + 1) / 2) (scalarSeq v)).PosSemidef) :
    (Q.map (Hs v) - Q.map (eval (sE v))).PosSemidef := by sorry

end RobustPMI.Hierarchy
