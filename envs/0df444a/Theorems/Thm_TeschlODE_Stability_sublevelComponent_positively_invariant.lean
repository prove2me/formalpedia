-- Prove2me | Theorems.Thm_TeschlODE_Stability_sublevelComponent_positively_invariant
-- name    : TeschlODE.Stability.sublevelComponent_positively_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T13:53:24.074258+00:00
-- url     : https://prove2.me/theorems/af2439ca-5f8b-4839-9867-a53f0bd7326a
-- title:
--   Lemma 6.11 — if $S_\delta$ is closed, it is positively invariant
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, $\Phi$ the flow with maximal intervals $I_x$, $x_0 \in M$ a fixed point ($f(x_0) = 0$), and $L$ a Liapunov function at $x_0$ on the open neighborhood $U \subseteq M$. Let $\delta \in \mathbb{R}$ and let $S_\delta$ be the connected component of $\{x \in U : L(x) \le \delta\}$ containing $x_0$. If $S_\delta$ is closed, then it is positively invariant (6.17):
--   $$\gamma_+(x) \subseteq S_\delta \qquad \text{for every } x \in S_\delta .$$
--
--   **Formalization Note.** "Closed" is closed in $\mathbb{R}^n$ (the book: $S_\delta$ may fail to be closed because it can share boundary with $U(x_0)$). The fixed point and the Liapunov function are the standing data of §6.6.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 201, Lemma 6.11 (positive invariance as in Eq. (6.17), p. 193)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_sublevelComponent

namespace TeschlODE.Stability

theorem sublevelComponent_positively_invariant {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) (δ : ℝ)
    (hclosed : IsClosed (sublevelComponent U L x₀ δ)) :
    ∀ x ∈ sublevelComponent U L x₀ δ,
      semiOrbit 1 I Φ x ⊆ sublevelComponent U L x₀ δ := by sorry

end TeschlODE.Stability
