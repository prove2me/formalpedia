-- Prove2me | Theorems.Thm_TeschlODE_Stability_sublevelComponent_ball
-- name    : TeschlODE.Stability.sublevelComponent_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T14:01:39.0564+00:00
-- url     : https://prove2.me/theorems/cc586f62-055d-402d-8d0c-5787758a35de
-- title:
--   Lemma 6.12 — $S_\varepsilon \subseteq B_\delta(x_0)$ and $B_\varepsilon(x_0) \subseteq S_\delta$ (6.37)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, $x_0 \in M$ a fixed point, and $L$ a Liapunov function at $x_0$ on the open neighborhood $U \subseteq M$; let $S_\delta$ be the connected component of $\{x \in U : L(x) \le \delta\}$ containing $x_0$. Then for every $\delta > 0$ there is an $\varepsilon > 0$ such that
--   $$S_\varepsilon \subseteq B_\delta(x_0) \quad\text{and}\quad B_\varepsilon(x_0) \subseteq S_\delta . \qquad (6.37)$$
--
--   **Formalization Note.** $B_r(x_0)$ is the open Euclidean ball (`Metric.ball`), the book's convention (§2.2). The lemma does not involve the flow, so no flow is a parameter; $f$ enters only through the Liapunov condition.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 201, Lemma 6.12 and Eq. (6.37)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_sublevelComponent

namespace TeschlODE.Stability

theorem sublevelComponent_ball {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      sublevelComponent U L x₀ ε ⊆ Metric.ball x₀ δ ∧
      Metric.ball x₀ ε ⊆ sublevelComponent U L x₀ δ := by sorry

end TeschlODE.Stability
