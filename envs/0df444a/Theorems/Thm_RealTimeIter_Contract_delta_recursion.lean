-- Prove2me | Theorems.Thm_RealTimeIter_Contract_delta_recursion
-- name    : RealTimeIter.Contract.delta_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:57.030516+00:00
-- url     : https://prove2.me/theorems/b388fda4-486c-458f-8db7-0254a839a513
-- title:
--   §4, proof of Theorem 4.1, p. 1722 — $\delta_{k+1}\le\delta_k\le\delta_0$ and $\|\Delta y^k\|_k\le(\delta_0)^k\|\Delta y^0\|_0$
-- statement:
--   Let $\kappa\in\mathbb R$, $\omega\ge0$, and let $(a_k)_{k\ge0}$ be nonnegative reals (the step norms $\|\Delta y^k\|_k$). Put $\delta_k:=\kappa+\frac{\omega}{2}a_k$. If $\delta_0<1$ and $a_{k+1}\le\delta_k a_k$ for every $k$, then for every $k$
--   $$\delta_{k+1}\le\delta_k,\qquad\delta_k\le\delta_0,\qquad a_k\le(\delta_0)^k a_0.$$
--
--   This is the inductive step that turns the one-step contraction into the geometric decay of the real-time steps used for (4.3), (4.2) and (4.4).
--
--   **Formalization Note.** Stated for an abstract sequence. The hypothesis $\omega\ge0$ is added: for $\omega<0$ the abstract statement is false, while in Theorem 4.1 a negative $\omega$ makes (4.1b) unsatisfiable on any domain with two points. The paper's intermediate product bound $\|\Delta y^k\|_k\le\delta_{k-1}\cdots\delta_0\|\Delta y^0\|_0$ is not stated separately.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), p. 1722, §4, proof of Theorem 4.1 (Contraction property and Well definedness), δ-recursion and the bound on ‖Δy^k‖_k

import Mathlib

namespace RealTimeIter.Contract

theorem delta_recursion (κ ω : ℝ) (hω : 0 ≤ ω) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hδ0 : κ + ω / 2 * a 0 < 1)
    (hrec : ∀ k, a (k + 1) ≤ (κ + ω / 2 * a k) * a k) :
    ∀ k, κ + ω / 2 * a (k + 1) ≤ κ + ω / 2 * a k ∧
      κ + ω / 2 * a k ≤ κ + ω / 2 * a 0 ∧
      a k ≤ (κ + ω / 2 * a 0) ^ k * a 0 := by sorry

end RealTimeIter.Contract
