-- Prove2me | Theorems.Thm_TeschlODE_Stability_krasovskii_lasalle
-- name    : TeschlODE.Stability.krasovskii_lasalle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T14:15:46.286217+00:00
-- url     : https://prove2.me/theorems/2f49f6dd-a5d9-429f-b41a-148c78da7475
-- title:
--   Theorem 6.14 (Krasovskii–LaSalle principle)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow of $\dot x = f(x)$ with maximal intervals $I_x$ and orbits $\gamma(y) = \Phi(I_y \times \{y\})$. Suppose $x_0 \in M$ is a fixed point of $f$ and $L$ is a Liapunov function at $x_0$ on the open neighborhood $U = U(x_0) \subseteq M$. Say that $L$ is **not constant on any orbit lying entirely in $U \setminus \{x_0\}$** if
--   $$\forall y \in M:\quad \gamma(y) \subseteq U \setminus \{x_0\} \ \Longrightarrow\ \exists\, a, b \in \gamma(y),\ L(a) \ne L(b). \qquad (\ast)$$
--   Then:
--
--   1. if $(\ast)$ holds, $x_0$ is asymptotically stable;
--   2. if $L$ is a strict Liapunov function, $(\ast)$ holds;
--   3. if $(\ast)$ holds, then every $x \in M$ whose forward orbit $\gamma_+(x)$ lies in a compact subset $C$ of $U$ has $\Phi(t, x)$ defined for all $t \ge 0$ and $\Phi(t, x) \to x_0$ as $t \to \infty$.
--
--   This is the central stability criterion of the chapter: asymptotic stability from a Liapunov function that is merely non-increasing, provided it is not constant on a whole orbit.
--
--   **Formalization Note.** The flow is local; no completeness is assumed anywhere. Part 3 **corrects** the book's "every orbit lying entirely in $U(x_0)$ converges to $x_0$", which is false as printed: for $\dot x_1 = -6x_1/(1+x_1^2)^2 + 2x_2$, $\dot x_2 = -2(x_1 + x_2)/(1+x_1^2)^2$ on $M = U = \mathbb{R}^2$, $L = x_1^2/(1+x_1^2) + x_2^2$ is a strict Liapunov function, yet orbits starting in $\{x_1 > \sqrt2,\ x_2 > 2/(x_1 - \sqrt2)\}$ stay in that region and do not converge to $0$ (Khalil, *Nonlinear Systems*, 3rd ed., §4.1). The book's argument (the text before Theorem 6.14) needs $\omega_+(x)$ to be a nonempty subset of $U$, which is exactly what a forward orbit inside a compact $C \subseteq U$ provides. Parts 1 and 2 are as printed.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 202, Theorem 6.14

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_IsStrictLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_orbit
import Definitions.Def_TeschlODE_Stability_IsStable
import Definitions.Def_TeschlODE_Stability_IsAsymptoticallyStable

namespace TeschlODE.Stability

theorem krasovskii_lasalle {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) :
    -- (i) L not constant on any orbit lying entirely in U \ {x₀} ⇒ x₀ asymptotically stable
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      IsAsymptoticallyStable M I Φ x₀) ∧
    -- (ii) a strict Liapunov function is not constant on any orbit lying entirely in U \ {x₀}
    (IsStrictLiapunovFunction f M x₀ U L →
      ∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) ∧
    -- (iii) under the hypothesis of (i), every forward orbit lying in a compact subset of U
    -- exists for all t ≥ 0 and converges to x₀
    ((∀ y ∈ M, orbit I Φ y ⊆ U \ {x₀} → ∃ a ∈ orbit I Φ y, ∃ b ∈ orbit I Φ y, L a ≠ L b) →
      ∀ x ∈ M, ∀ C : Set (EuclideanSpace ℝ (Fin n)), IsCompact C → C ⊆ U →
        semiOrbit 1 I Φ x ⊆ C →
        (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
          Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds x₀)) := by sorry

end TeschlODE.Stability
