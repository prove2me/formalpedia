-- Prove2me | Theorems.Thm_TeschlODE_Planar_intersections_monotone
-- name    : TeschlODE.Planar.intersections_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:19:16.717454+00:00
-- url     : https://prove2.me/theorems/8f926862-33f6-4cb9-b12e-3a7660a06664
-- title:
--   Lemma 7.9 — intersections of an orbit with a transversal arc are monotone
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $\sigma \in \{\pm\}$, $x_0 \in M$ a regular point ($f(x_0) \neq 0$) and $\Sigma = s(J)$ a transversal arc containing $x_0$. Let $t_1, t_2, \dots$ be the times $t \in I_{x_0}$ with $\sigma t > 0$ at which $x_n = \Phi(t_n, x_0) \in \Sigma$, ordered according to $t_n$ (the sequence may be finite). Then $(x_n)$ is monotone with respect to the order of $\Sigma$:
--   $$ s^{-1}(x_1),\ s^{-1}(x_2),\ \dots \quad \text{is monotone.}$$
--
--   This is the planar ingredient of the whole section: it rests on the Jordan curve theorem and fails in dimension three.
--
--   **Formalization Note.** Instead of a sequence, the statement quantifies over any function $u$ that gives the arc parameter $u(t) \in J$, $s(u(t)) = \Phi(t, x_0)$, of every intersection time $t$ (unique, since $s$ is injective), and asserts that $u$ is monotone or antitone on the set of intersection times. For $\sigma = -$ this is the same as monotonicity of the sequence ordered by decreasing time. As in the book's statement, $n \ge 1$: the time $t = 0$ is not an intersection time.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 221, Lemma 7.9

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow
import Definitions.Def_TeschlODE_Planar_IsTransversalArc

namespace TeschlODE.Planar

/-- Teschl, Lemma 7.9 (p. 221): let `M ⊆ ℝ²` be open, `f ∈ C¹(M, ℝ²)`, `x₀ ∈ M` a regular point
(`f x₀ ≠ 0`) and `Σ = s(J)` a transversal arc containing `x₀`. The intersection times of the
half-orbit `γ_σ(x₀)` with `Σ` are the `t ∈ I_{x₀}` with `σ t > 0` (`σ = true`: `t > 0`;
`σ = false`: `t < 0`) and `Φ(t, x₀) ∈ Σ`. If `u t ∈ J` is the arc parameter of the intersection
point `Φ(t, x₀) = s(u t)` at every such time, then `u` is monotone or antitone on the set of
intersection times, i.e. the sequence of intersections, ordered by time, is monotone with respect
to the order of `Σ`. -/
theorem intersections_monotone {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ∈ M) (hreg : f x₀ ≠ 0)
    {J : Set ℝ} {s : ℝ → Fin 2 → ℝ} (harc : IsTransversalArc f M J s) (hx₀arc : x₀ ∈ s '' J)
    (u : ℝ → ℝ)
    (hu : ∀ t, t ∈ lifetime f M x₀ → (if σ then 0 < t else t < 0) → flow f M t x₀ ∈ s '' J →
      u t ∈ J ∧ s (u t) = flow f M t x₀) :
    MonotoneOn u {t | t ∈ lifetime f M x₀ ∧ (if σ then 0 < t else t < 0) ∧ flow f M t x₀ ∈ s '' J} ∨
      AntitoneOn u
        {t | t ∈ lifetime f M x₀ ∧ (if σ then 0 < t else t < 0) ∧ flow f M t x₀ ∈ s '' J} := by sorry

end TeschlODE.Planar
