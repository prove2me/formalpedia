-- Prove2me | Theorems.Thm_RobustLS_Unstructured_worst_case_residual_spectral
-- name    : RobustLS.Unstructured.worst_case_residual_spectral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:26:00.164752+00:00
-- url     : https://prove2.me/theorems/867b8184-af3e-4e57-8c32-c8ce008006b3
-- title:
--   p. 1040 — the worst-case residual is the same for the largest-singular-value norm
-- statement:
--   Let $n \ge 1$, $A \in \mathbb{R}^{n\times m}$, $b \in \mathbb{R}^n$ and $x \in \mathbb{R}^m$. If the perturbation bound in (1) is measured in the largest singular value norm $\|\cdot\|$ instead of the Frobenius norm, the worst-case residual is unchanged:
--
--   $$
--   \max_{\|[\Delta A\ \Delta b]\| \le 1} \|(A+\Delta A)x - (b+\Delta b)\| = \|Ax-b\| + \sqrt{\|x\|^2+1}.
--   $$
--
--   Since $\|\Delta\| \le \|\Delta\|_F$, the spectral ball contains the Frobenius ball; the statement says that the larger ball does not produce a larger worst case.
--
--   **Formalization Note** The maximum is encoded as the supremum of the attained residuals (nonempty and bounded above). The hypothesis $n \ge 1$ excludes the empty system, for which the only perturbation is the empty matrix and the worst case is $0$. The paper normalizes $\rho = 1$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, §3 (remark before §3.1) and Theorem 3.1, proof

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- El Ghaoui & Lebret (1997), p. 1040 (PDF p. 6): "the worst-case residual is the same when
the norm used is the largest singular value norm". With `ρ = 1` and `n ≥ 1`, the worst case
over `‖[ΔA Δb]‖ ≤ 1` (largest singular value) is `‖Ax − b‖ + √(‖x‖² + 1)`, the same value as
for the Frobenius ball (Theorem 3.1). The assumption `0 < n` excludes the empty system, where
the only perturbation is the empty matrix and the worst case is `0`. -/
theorem worst_case_residual_spectral {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) :
    worstCaseResidualSpec A b 1 x = eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Unstructured
