-- Prove2me | Theorems.Thm_RobustLS_LinFrac_residualBelow_iff_lmi
-- name    : RobustLS.LinFrac.residualBelow_iff_lmi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:39:58.776812+00:00
-- url     : https://prove2.me/theorems/a9a0d705-5680-4f9e-9248-dbcc49b5ebf7
-- title:
--   §5.4, p. 1047 — λ > r_𝒟(A, b, x) iff det(I − DΔ) ≠ 0 and a linear-fractional LMI holds for every Δ ∈ 𝒟, ‖Δ‖ ≤ 1
-- statement:
--   In the linear-fractional model of §5.2 (subspace $\mathcal D \subseteq \mathbb R^{N\times N}$, data $A, b, L, R_A, R_b, D$, and $\rho = 1$), fix $x \in \mathbb R^m$ and $\lambda \in \mathbb R$. Then $\lambda > r_{\mathcal D}(A,b,x)$ if and only if, for every $\Delta \in \mathcal D$ with $\|\Delta\| \le 1$, $\det(I - D\Delta) \neq 0$ and
--
--   $$
--   \begin{bmatrix} \lambda I & Ax - b \\ (Ax-b)^T & \lambda \end{bmatrix} + \begin{bmatrix} L \\ 0 \end{bmatrix}\Delta(I - D\Delta)^{-1}\begin{bmatrix} 0 & R_Ax - R_b \end{bmatrix} + \begin{bmatrix} 0 \\ (R_Ax - R_b)^T \end{bmatrix}(I - D\Delta)^{-T}\Delta^T\begin{bmatrix} L^T & 0 \end{bmatrix} \succ 0 .
--   $$
--
--   Here $r_{\mathcal D}(A,b,x) = +\infty$ when some admissible $\Delta$ makes $I - D\Delta$ singular, in which case both sides are false.
--
--   This recasts the worst-case residual bound as robust positivity of a linear-fractional matrix function, in the form of (9), so that Lemma 2.3 applies.
--
--   **Formalization Note** "$\lambda > r_{\mathcal D}(A,b,x)$" is the predicate `ResidualBelow` of the definition module (for every admissible $\Delta$: $\det(I-D\Delta) \ne 0$ and $\|A(\Delta)x - b(\Delta)\| < \lambda$), which represents the value $+\infty$ of (35) exactly.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1047, §5.4 (display after Eq. (37))

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §5.4, p. 1047 (PDF p. 13): "Let λ ∈ ℝ. The inequality
λ > r_𝒟(A, b, x) holds if and only if, for every Δ ∈ 𝒟, ‖Δ‖ ≤ 1, we have det(I − DΔ) ≠ 0 and
[[λI, Ax − b], [(Ax − b)ᵀ, λ]] + [L; 0]Δ(I − DΔ)⁻¹[0  R_Ax − R_b]
+ [0; (R_Ax − R_b)ᵀ](I − DΔ)⁻ᵀΔᵀ[Lᵀ  0] > 0."
Here `ResidualBelow` encodes `λ > r_𝒟(A, b, x)` with `ρ = 1`, including the value `∞` of (35). -/
theorem residualBelow_iff_lmi {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    ResidualBelow 𝒟 A b L RA Rb D x lam ↔
      ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧ (residualLMI A b L RA Rb D x lam Δ).PosDef := by sorry

end RobustLS.LinFrac
