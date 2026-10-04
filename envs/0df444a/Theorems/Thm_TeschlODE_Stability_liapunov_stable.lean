-- Prove2me | Theorems.Thm_TeschlODE_Stability_liapunov_stable
-- name    : TeschlODE.Stability.liapunov_stable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T14:08:42.050425+00:00
-- url     : https://prove2.me/theorems/09e66f7c-3738-4c1a-b315-82b040f6b0e8
-- title:
--   Theorem 6.13 (Liapunov) — a Liapunov function makes the fixed point stable
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow of $\dot x = f(x)$ with maximal intervals $I_x$. Suppose $x_0 \in M$ is a fixed point of $f$, $f(x_0) = 0$. If there is a Liapunov function $L$ at $x_0$ (on an open neighborhood $U \subseteq M$ of $x_0$, in the sense of (6.35)–(6.36)), then $x_0$ is stable: for every neighborhood $U'$ of $x_0$ there is a neighborhood $V \subseteq U'$ of $x_0$ such that for all $x \in V$,
--   $$\Phi(t, x) \text{ is defined and } \Phi(t, x) \in U' \quad \text{for all } t \ge 0 .$$
--
--   **Formalization Note.** The flow is local (no completeness is assumed); existence of the solution for all $t \ge 0$ is part of the conclusion, see the definition of stability.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 201, Theorem 6.13

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_IsStable

namespace TeschlODE.Stability

theorem liapunov_stable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    IsStable M I Φ x₀ := by sorry

end TeschlODE.Stability
