-- Prove2me | Theorems.Thm_TeschlODE_IVP_picard_lindelof
-- name    : TeschlODE.IVP.picard_lindelof
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:07.443964+00:00
-- url     : https://prove2.me/theorems/d1c5c517-32f1-438d-8766-6482cc5eb3d5
-- title:
--   Theorem 2.2 (Picard–Lindelöf) — local existence, uniqueness, and existence time T₀ = min{T, δ/M}
-- statement:
--   Let $U \subseteq \mathbb{R} \times \mathbb{R}^n$ be open, $f$ continuous on $U$, $(t_0, x_0) \in U$, and suppose $f$ is locally Lipschitz continuous in the second argument, uniformly with respect to the first, on $U$. Then:
--
--   1. **(local existence)** there is $\varepsilon > 0$ and a solution $x$ of $\dot x = f(t,x)$ on $(t_0 - \varepsilon, t_0 + \varepsilon)$ with graph in $U$ and $x(t_0) = x_0$;
--   2. **(uniqueness)** on every interval $I \ni t_0$, any two solutions on $I$ with graph in $U$ and value $x_0$ at $t_0$ coincide on $I$;
--   3. **(existence time)** if $T, \delta > 0$, $V = [t_0, t_0 + T] \times \bar B_\delta(x_0) \subseteq U$ and $M = \max_{V} |f|$, then there is a solution $x$ with $x(t_0) = x_0$ on $[t_0, t_0 + T_0]$ whose graph stays in $V$ (so $|x(t) - x_0| \le \delta$), where
--   $$T_0 = \min\Bigl\{T, \frac{\delta}{M}\Bigr\}, \qquad \frac{\delta}{M} = \infty \text{ if } M = 0; \qquad (2.16)$$
--   4. the analogous statement holds on $[t_0 - T_0, t_0]$ with $V = [t_0 - T, t_0] \times \bar B_\delta(x_0)$.
--
--   Together with uniqueness, item 3 says the unique solution exists at least on $[t_0, t_0 + T_0]$.
--
--   **Formalization Note.** The book writes $V = [t_0, t_0+T] \times B_\delta(x_0)$ with the open ball and "the maximum of $|f|$ on $V$", and says the solution "remains in $B_\delta(x_0)$". A maximum over the open ball need not exist, and the solution can reach the sphere $|x - x_0| = \delta$ at $t = t_0 + T_0$ (e.g. $n = 1$, $f \equiv 1$, $\delta = 1$, $T = 2$). The statement therefore uses the closed ball $\bar B_\delta(x_0)$, as the book's own proof on p. 37 does ($C = \{x : \|x - x_0\| \le \delta\}$). $M$ is given as the greatest element of $\{|f(p)| : p \in V\}$. $T_0$ is written `if M = 0 then T else min T (δ / M)`, the book's convention $\delta/0 = \infty$. The book's final sentence says "$[t_0 - T, t_0]$"; the statement uses $[t_0 - T_0, t_0]$, the evident intended reading. "Some interval around $t_0$" is read as $\exists \varepsilon > 0$ with the open interval $(t_0 - \varepsilon, t_0 + \varepsilon)$; "unique" is read as uniqueness on every interval containing $t_0$ (sets $I$ that are order-connected).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 38, Theorem 2.2

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn
import Definitions.Def_TeschlODE_IVP_LocallyLipschitzSecond

namespace TeschlODE.IVP

theorem picard_lindelof {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContinuousOn f U)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (h₀ : (t₀, x₀) ∈ U)
    (hLip : LocallyLipschitzSecond U f) :
    -- local existence on an open interval around `t₀`
    (∃ ε : ℝ, 0 < ε ∧ ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
      IsSolutionOn U f (Set.Ioo (t₀ - ε) (t₀ + ε)) x) ∧
    -- uniqueness on every interval containing `t₀`
    (∀ I : Set ℝ, I.OrdConnected → t₀ ∈ I →
      ∀ x y : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ → y t₀ = x₀ →
        IsSolutionOn U f I x → IsSolutionOn U f I y → Set.EqOn x y I) ∧
    -- existence time `T₀ = min {T, δ / M}` forward in time
    (∀ T δ M : ℝ, 0 < T → 0 < δ →
      Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ ⊆ U →
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        IsSolutionOn (Set.Icc t₀ (t₀ + T) ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc t₀ (t₀ + (if M = 0 then T else min T (δ / M)))) x) ∧
    -- and backward in time
    (∀ T δ M : ℝ, 0 < T → 0 < δ →
      Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ ⊆ U →
      IsGreatest ((fun p => ‖f p‖) '' (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ)) M →
      ∃ x : ℝ → EuclideanSpace ℝ (Fin n), x t₀ = x₀ ∧
        IsSolutionOn (Set.Icc (t₀ - T) t₀ ×ˢ Metric.closedBall x₀ δ) f
          (Set.Icc (t₀ - (if M = 0 then T else min T (δ / M))) t₀) x) := by sorry

end TeschlODE.IVP
