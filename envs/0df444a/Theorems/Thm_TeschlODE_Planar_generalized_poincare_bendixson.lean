-- Prove2me | Theorems.Thm_TeschlODE_Planar_generalized_poincare_bendixson
-- name    : TeschlODE.Planar.generalized_poincare_bendixson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T15:56:03.390048+00:00
-- url     : https://prove2.me/theorems/ae33e1e9-60b3-4e46-a184-1ef83e4dd039
-- title:
--   Theorem 7.16 — generalized Poincaré–Bendixson theorem
-- statement:
--   Let $M$ be an open subset of $\mathbb{R}^2$ and $f \in C^1(M, \mathbb{R}^2)$. Fix $x \in M$ and $\sigma \in \{\pm\}$, and suppose $\omega_\sigma(x) \neq \emptyset$ is compact, connected, and contains only finitely many fixed points. Then one of the following holds:
--
--   $$\text{(i) } \omega_\sigma(x) \text{ is a fixed orbit;}\quad \text{(ii) } \omega_\sigma(x) \text{ is a regular periodic orbit;}$$
--   $$\text{(iii) } \omega_\sigma(x) \text{ consists of finitely many fixed points } \{x_j\} \text{ and non-closed orbits } \gamma(y) \text{ with } \omega_\pm(y) \in \{x_j\}.$$
--
--   This classifies all compact connected limit sets of planar flows with finitely many equilibria; it is the capstone of Chapter 7.
--
--   **Formalization Note.** $\sigma$ is a `Bool` (`true` = $+$). (i) is $\omega_\sigma(x) = \{x_0\}$ with $f(x_0) = 0$. (ii) is $\omega_\sigma(x) = \gamma(y)$ with $y$ periodic and $f(y) \neq 0$. (iii) is: every $y \in \omega_\sigma(x)$ with $f(y) \neq 0$ lies on a non-closed orbit ($y$ not periodic) with $\gamma(y) \subseteq \omega_\sigma(x)$, and $\omega_+(y) = \{a\}$, $\omega_-(y) = \{b\}$ for fixed points $a, b \in \omega_\sigma(x)$ (the book's "$\omega_\pm(y) \in \{x_j\}$", a one-point set identified with its point). "Only finitely many fixed points" is `Set.Finite` of $\{y \in \omega_\sigma(x) : f(y) = 0\}$; "connected" is `IsPreconnected` together with the separate nonemptiness hypothesis.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 223–224, Theorem 7.16

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint

namespace TeschlODE.Planar

/-- Teschl, Theorem 7.16 (generalized Poincaré–Bendixson, pp. 223–224): let `M ⊆ ℝ²` be open,
`f ∈ C¹(M, ℝ²)`, `x ∈ M`, `σ ∈ {±}`, and suppose `ω_σ(x)` is nonempty, compact, connected and
contains only finitely many fixed points. Then
(i) `ω_σ(x)` is a fixed orbit `{x₀}` with `f x₀ = 0`; or
(ii) `ω_σ(x) = γ(y)` is a regular periodic orbit (`y` periodic, `f y ≠ 0`); or
(iii) every point `y ∈ ω_σ(x)` is a fixed point or lies on a non-closed orbit `γ(y) ⊆ ω_σ(x)`
whose limit sets `ω₊(y)` and `ω₋(y)` are single fixed points of `ω_σ(x)`. -/
theorem generalized_poincare_bendixson {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    (hne : (omegaLimitSet f M σ x).Nonempty) (hcpt : IsCompact (omegaLimitSet f M σ x))
    (hconn : IsPreconnected (omegaLimitSet f M σ x))
    (hfin : {y | y ∈ omegaLimitSet f M σ x ∧ f y = 0}.Finite) :
    (∃ x₀, f x₀ = 0 ∧ omegaLimitSet f M σ x = {x₀}) ∨
    (∃ y, IsPeriodicPoint f M y ∧ f y ≠ 0 ∧ omegaLimitSet f M σ x = orbit f M y) ∨
    (∀ y ∈ omegaLimitSet f M σ x, f y = 0 ∨
      (orbit f M y ⊆ omegaLimitSet f M σ x ∧ ¬ IsPeriodicPoint f M y ∧
        ∃ a ∈ omegaLimitSet f M σ x, ∃ b ∈ omegaLimitSet f M σ x, f a = 0 ∧ f b = 0 ∧
          omegaLimitSet f M true y = {a} ∧ omegaLimitSet f M false y = {b})) := by sorry

end TeschlODE.Planar
