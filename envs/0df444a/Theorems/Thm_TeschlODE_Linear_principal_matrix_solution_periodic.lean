-- Prove2me | Theorems.Thm_TeschlODE_Linear_principal_matrix_solution_periodic
-- name    : TeschlODE.Linear.principal_matrix_solution_periodic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:56:09.686024+00:00
-- url     : https://prove2.me/theorems/bde45006-73da-4ee1-8f38-5f397db8e4f6
-- title:
--   Lemma 3.14 — Π(t + T, t₀ + T) = Π(t, t₀) for T-periodic A
-- statement:
--   Let $A \in C(\mathbb{R}, \mathbb{R}^{n\times n})$ be periodic, $A(t+T) = A(t)$ for all $t$, with $T > 0$ (3.117), and let $\Phi$ be the principal matrix solution of $\dot x = A(t)x$ on $\mathbb{R}$. Then
--   $$\Phi(t+T, t_0+T) = \Phi(t, t_0) \qquad \text{for all } t, t_0 \in \mathbb{R}. \qquad (3.118)$$
--
--   Consequently the monodromy matrix $M(t_0) = \Phi(t_0+T, t_0)$ is $T$-periodic in $t_0$ and $\Phi(t_0 + \ell T, t_0) = M(t_0)^\ell$; this is the first step towards Floquet's theorem.
--
--   **Formalization Note.** Section 3.6 works on $I = \mathbb{R}$; the principal matrix solution is `IsPrincipalMatrixSolution A Set.univ Φ`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 91, Lemma 3.14

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

namespace TeschlODE.Linear

/-- Teschl, Lemma 3.14 (p. 91): if `A ∈ C(ℝ, ℝ^{n×n})` is periodic, `A(t + T) = A(t)` with
`T > 0` (3.117), then the principal matrix solution satisfies `Φ(t + T, t₀ + T) = Φ(t, t₀)`
(3.118). -/
theorem principal_matrix_solution_periodic {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hper : ∀ t, A (t + T) = A t)
    (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsPrincipalMatrixSolution A Set.univ Φ)
    (t t₀ : ℝ) :
    Φ (t + T) (t₀ + T) = Φ t t₀ := by sorry

end TeschlODE.Linear
