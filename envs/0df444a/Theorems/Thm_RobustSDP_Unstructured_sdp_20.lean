-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_sdp_20
-- name    : RobustSDP.Unstructured.sdp_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:09:31.951955+00:00
-- url     : https://prove2.me/theorems/640a3b7b-94e5-4c43-993c-308da51da64f
-- title:
--   §5.1, Eq. (20) — the robust LMI under unstructured perturbations as an SDP in $(x, \tau)$
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$, let $\rho > 0$, and consider the unstructured perturbation $\mathbf{F}(x,\Delta) = F(x) + \Delta_0 + \Delta_0^T + \sum_i x_i(\Delta_i + \Delta_i^T)$ with $\Delta = [\Delta_0 \cdots \Delta_m] \in \mathbb{R}^{n\times n(m+1)}$. Then for every $x \in \mathbb{R}^m$, $\mathbf{F}(x,\Delta) \succeq 0$ for every $\Delta$ with $\|\Delta\| \le \rho$ if and only if there is a scalar $\tau$ with
--   $$\begin{bmatrix} F(x) - \tau I & [1\ \ x^T]\otimes \rho I \\ [1\ \ x^T]^T \otimes \rho I & \tau I \end{bmatrix} \succeq 0 .$$
--
--   Consequently the robust SDP "minimize $c^Tx$ over the robust feasible set" and the SDP (20) in the variables $(x,\tau)$ have the same optimal value, and their solutions correspond by projection onto $x$. This is the first step of the paper's derivation of the closed-form counterpart (21).
--
--   **Formalization Note** The statement is the set identity behind the paper's "problem (4) is equivalent to the SDP (20)", stated for every $x$. $\|\Delta\|$ is the largest singular value of the whole block row. The paper attributes the equivalence to Lemma 3.2 and refers to "section 5"; the exact (if-and-only-if) result applied here is the full-perturbation case (Theorem 3.1 with $L = I$, $D = 0$, the second block row and column scaled by $\rho$), and the representation is that of §2.2.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 41, §5.1, Eq. (19) and Eq. (20)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- (19)–(20), §5.1, p. 41: under unstructured perturbations, `x` is robustly feasible iff
there is a scalar `τ` making the block matrix of (20) positive semidefinite. -/
theorem sdp_20 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs ρ ↔ ∃ τ : ℝ, (lmi20 Fs ρ τ x).PosSemidef := by sorry

end RobustSDP.Unstructured
