-- Prove2me | Theorems.Thm_TeschlODE_Planar_unique_connecting_orbit
-- name    : TeschlODE.Planar.unique_connecting_orbit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:52:21.399387+00:00
-- url     : https://prove2.me/theorems/0c4f6a35-bb3f-487d-afbd-e018620d081b
-- title:
--   Lemma 7.15 — at most one orbit in ω_σ(x) connects two given fixed points
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $x \in M$, $\sigma \in \{\pm\}$, and suppose $\omega_\sigma(x)$ is compact. Let $x_\pm \in \omega_\sigma(x)$ be distinct fixed points. Then there exists at most one orbit $\gamma(y) \subseteq \omega_\sigma(x)$ with
--   $$\omega_+(y) = \{x_+\}, \qquad \omega_-(y) = \{x_-\}.$$
--
--   **Formalization Note.** "At most one" is stated as: two such orbits $\gamma(y_1), \gamma(y_2)$ are equal. The book's $\omega_\pm(y) = x_\pm$ identifies a one-point set with its point.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 223, Lemma 7.15

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet

namespace TeschlODE.Planar

/-- Teschl, Lemma 7.15 (p. 223): let `M ⊆ ℝ²` be open, `f ∈ C¹(M, ℝ²)`, `x ∈ M`, `σ ∈ {±}`, and
suppose `ω_σ(x)` is compact. Let `x₊ ≠ x₋` be fixed points in `ω_σ(x)`. Then there is at most one
orbit `γ(y) ⊆ ω_σ(x)` with `ω₊(y) = {x₊}` and `ω₋(y) = {x₋}`: any two such orbits coincide. -/
theorem unique_connecting_orbit {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M) (hcpt : IsCompact (omegaLimitSet f M σ x))
    {xp xm : Fin 2 → ℝ} (hxp : xp ∈ omegaLimitSet f M σ x) (hxm : xm ∈ omegaLimitSet f M σ x)
    (hfxp : f xp = 0) (hfxm : f xm = 0) (hne : xp ≠ xm)
    {y₁ y₂ : Fin 2 → ℝ}
    (h₁ : orbit f M y₁ ⊆ omegaLimitSet f M σ x)
    (h₁p : omegaLimitSet f M true y₁ = {xp}) (h₁m : omegaLimitSet f M false y₁ = {xm})
    (h₂ : orbit f M y₂ ⊆ omegaLimitSet f M σ x)
    (h₂p : omegaLimitSet f M true y₂ = {xp}) (h₂m : omegaLimitSet f M false y₂ = {xm}) :
    orbit f M y₁ = orbit f M y₂ := by sorry

end TeschlODE.Planar
