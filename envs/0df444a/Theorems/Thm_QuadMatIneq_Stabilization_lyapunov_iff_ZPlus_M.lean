-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_lyapunov_iff_ZPlus_M
-- name    : QuadMatIneq.Stabilization.lyapunov_iff_ZPlus_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:25.794881+00:00
-- url     : https://prove2.me/theorems/c97595ea-e110-4de5-b457-21ba20f3f3f8
-- title:
--   §5.1, p. 18 — for fixed P > 0 and K, the Lyapunov inequality (2.4) holds iff [A B]ᵀ ∈ 𝒵⁺_{n+m}(M) with M of (5.1)
-- statement:
--   Fix a Lyapunov matrix $P\in\mathbb{R}^{n\times n}$, $P>0$, and a feedback gain $K\in\mathbb{R}^{m\times n}$, and let $M$ be the matrix (5.1),
--   $$M=\begin{bmatrix}P&0&0\\0&-P&-PK^\top\\0&-KP&-KPK^\top\end{bmatrix}.$$
--   Then for all $A\in\mathbb{R}^{n\times n}$, $B\in\mathbb{R}^{n\times m}$,
--   $$P-(A+BK)P(A+BK)^\top>0\iff\begin{bmatrix}A&B\end{bmatrix}^{\top}\in\mathcal Z^+_{n+m}(M).$$
--
--   Together with $\Sigma=\mathcal Z_{n+m}(N)$, this turns informativity for quadratic stabilization into the inclusion $\mathcal Z_{n+m}(N)\subseteq\mathcal Z^+_{n+m}(M)$, (5.3).
--
--   **Formalization Note** $[A\ B]^\top$ is `Matrix.fromRows Aᵀ Bᵀ`; $M$ is `Mmat P K`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §5.1, p. 18, sentence after (5.2) ("The inequality (2.4) is equivalent to [A B]ᵀ ∈ 𝒵⁺_{n+m}(M)")

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI
import Definitions.Def_QuadMatIneq_Stabilization_Data

open Matrix Filter Topology

namespace QuadMatIneq.Stabilization

/-- §5.1, p. 18: for a fixed Lyapunov matrix `P > 0` and feedback gain `K`, inequality (2.4)
is equivalent to `[A B]ᵀ ∈ 𝒵⁺_{n+m}(M)`. -/
theorem lyapunov_iff_ZPlus_M {n m : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (K : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (P - (A + B * K) * P * (A + B * K)ᵀ).PosDef ↔ Matrix.fromRows Aᵀ Bᵀ ∈ ZPlus (Mmat P K) := by sorry

end QuadMatIneq.Stabilization
