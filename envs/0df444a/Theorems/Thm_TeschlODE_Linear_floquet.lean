-- Prove2me | Theorems.Thm_TeschlODE_Linear_floquet
-- name    : TeschlODE.Linear.floquet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:58:20.142906+00:00
-- url     : https://prove2.me/theorems/c3eec27a-e1d9-4b19-96b3-4408704cfe8d
-- title:
--   Theorem 3.15 (Floquet) — Π(t, t₀) = P(t, t₀) exp((t − t₀)Q(t₀)) with P periodic
-- statement:
--   Let $A \in C(\mathbb{R}, \mathbb{R}^{n\times n})$ be periodic, $A(t+T) = A(t)$ with $T > 0$, and let $\Phi$ be the principal matrix solution of $\dot x = A(t)x$ (the book's $\Pi$). Then for every $t_0 \in \mathbb{R}$ there are a matrix $Q(t_0) \in \mathbb{C}^{n\times n}$ and a matrix function $P(\cdot,t_0) : \mathbb{R} \to \mathbb{C}^{n\times n}$ such that
--   $$\Phi(t,t_0) = P(t,t_0)\,\exp\big((t-t_0)\,Q(t_0)\big) \quad (t \in \mathbb{R}), \qquad (3.125)$$
--   where $P(\cdot, t_0)$ has the same period $T$ as $A$, $P(t+T, t_0) = P(t,t_0)$, and $P(t_0,t_0) = \mathbb{I}$.
--
--   Floquet's theorem says that a periodic linear system is, up to a periodic change of variables, a system with constant coefficients: the long-time behaviour of all solutions is governed by the eigenvalues of $Q(t_0)$ (the Floquet exponents), equivalently of the monodromy matrix $M(t_0) = \Phi(t_0+T,t_0) = \exp(TQ(t_0))$ (the Floquet multipliers).
--
--   **Formalization Note.** $Q(t_0)$ and $P$ are complex: the book notes (p. 92) that $Q(t_0)$ "will be complex even if $A(t)$ is real unless all real eigenvalues of $M(t_0)$ are positive"; the real version with period $2T$ is Corollary 3.16, which is a different statement and not part of this item. $\Phi(t,t_0)$ is real and is compared with the complex product after coercing its entries (`Matrix.map` by `ℝ → ℂ`). The periodicity of $P$ uses the same $T > 0$ as $A$; without it the statement would be trivial ($Q = 0$, $P = \Phi$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 92, Theorem 3.15

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

namespace TeschlODE.Linear

/-- Teschl, Theorem 3.15 (Floquet), p. 92: let `A ∈ C(ℝ, ℝ^{n×n})` be periodic with period
`T > 0` (3.117) and let `Φ` be the principal matrix solution of `ẋ = A(t) x`. Then for every
`t₀` there are a complex matrix `Q(t₀)` and a complex matrix function `P(·, t₀)` with the same
period `T` as `A` and `P(t₀, t₀) = I` such that `Φ(t, t₀) = P(t, t₀) exp((t − t₀) Q(t₀))`
for all `t` (3.125), `Φ(t, t₀)` being regarded as a complex matrix. -/
theorem floquet {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (hA : Continuous A) (T : ℝ)
    (hT : 0 < T) (hper : ∀ t, A (t + T) = A t) (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ : IsPrincipalMatrixSolution A Set.univ Φ) (t₀ : ℝ) :
    ∃ (P : ℝ → Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, P (t + T) = P t) ∧ P t₀ = 1 ∧
      ∀ t, (Φ t t₀).map (fun r : ℝ => (r : ℂ)) =
        P t * NormedSpace.exp (((t - t₀ : ℝ) : ℂ) • Q) := by sorry

end TeschlODE.Linear
