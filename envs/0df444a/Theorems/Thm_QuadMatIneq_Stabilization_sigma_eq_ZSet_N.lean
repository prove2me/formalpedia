-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_sigma_eq_ZSet_N
-- name    : QuadMatIneq.Stabilization.sigma_eq_ZSet_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:15.678301+00:00
-- url     : https://prove2.me/theorems/d234ced5-041a-4cdb-bb19-489226ce10f4
-- title:
--   §5.1, p. 18 — Σ = 𝒵_{n+m}(N): (A, B) is compatible with the data iff [A B]ᵀ solves the QMI defined by N of (5.2)
-- statement:
--   Let $\Phi\in\mathbb{R}^{(n+T)\times(n+T)}$, let $X\in\mathbb{R}^{n\times(T+1)}$ and $U_-\in\mathbb{R}^{m\times T}$ be data, and let $N$ be the matrix (5.2),
--   $$N=\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\end{bmatrix}\Phi\begin{bmatrix}I&X_+\\0&-X_-\\0&-U_-\end{bmatrix}^{\!\top}.$$
--   Then for all $A\in\mathbb{R}^{n\times n}$, $B\in\mathbb{R}^{n\times m}$,
--   $$(A,B)\in\Sigma\iff\begin{bmatrix}A&B\end{bmatrix}^{\top}\in\mathcal Z_{n+m}(N).$$
--
--   This identity, which the paper recalls from Section 2 and (2.5), recasts the set of systems consistent with the noisy data as the solution set of a single quadratic matrix inequality in $(A,B)$.
--
--   **Formalization Note** $[A\ B]^\top\in\mathbb{R}^{(n+m)\times n}$ is `Matrix.fromRows Aᵀ Bᵀ`; $\Sigma$, $N$ and $\mathcal Z$ are `Sigma`, `Nmat` and `ZSet` of the definitions items.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §5.1, p. 18, sentence after (5.2) ("Recall from Section 2 and (2.5) that Σ = 𝒵_{n+m}(N)")

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI
import Definitions.Def_QuadMatIneq_Stabilization_Data

open Matrix Filter Topology

namespace QuadMatIneq.Stabilization

/-- §5.1, p. 18: "Σ = 𝒵_{n+m}(N)", with `[A B]ᵀ ∈ ℝ^{(n+m)×n}` written `fromRows Aᵀ Bᵀ`. -/
theorem sigma_eq_ZSet_N {n m T : ℕ}
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A, B) ∈ Sigma Φ X Um ↔ Matrix.fromRows Aᵀ Bᵀ ∈ ZSet (Nmat Φ X Um) := by sorry

end QuadMatIneq.Stabilization
