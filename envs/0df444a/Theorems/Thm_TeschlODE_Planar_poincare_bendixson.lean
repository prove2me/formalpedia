-- Prove2me | Theorems.Thm_TeschlODE_Planar_poincare_bendixson
-- name    : TeschlODE.Planar.poincare_bendixson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:41:05.470098+00:00
-- url     : https://prove2.me/theorems/c4b74d59-7651-4ccc-8d26-e95fc6983f43
-- title:
--   Lemma 7.13 (Poincaré–Bendixson) — a compact ω-limit set without fixed points is a periodic orbit
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $x \in M$ and $\sigma \in \{\pm\}$. If $\omega_\sigma(x) \neq \emptyset$ is compact and contains no fixed points, then $\omega_\sigma(x)$ is a regular periodic orbit:
--   $$\omega_\sigma(x) = \gamma(y) \quad \text{for some periodic } y \text{ with } f(y) \neq 0 .$$
--
--   This is the classical Poincaré–Bendixson theorem, the tool for proving existence of limit cycles in planar systems.
--
--   **Formalization Note.** "No fixed points" is $f(y) \neq 0$ for all $y \in \omega_\sigma(x)$ (fixed point: $f(y) = 0$, p. 190).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 222, Lemma 7.13

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint

namespace TeschlODE.Planar

/-- Teschl, Lemma 7.13 (Poincaré–Bendixson theorem, p. 222): for `M ⊆ ℝ²` open,
`f ∈ C¹(M, ℝ²)`, `x ∈ M` and `σ ∈ {±}`, if `ω_σ(x)` is nonempty, compact and contains no fixed
point, then `ω_σ(x)` is a regular periodic orbit: `ω_σ(x) = γ(y)` for a periodic point `y` with
`f y ≠ 0`. -/
theorem poincare_bendixson {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    (hne : (omegaLimitSet f M σ x).Nonempty) (hcpt : IsCompact (omegaLimitSet f M σ x))
    (hnofix : ∀ y ∈ omegaLimitSet f M σ x, f y ≠ 0) :
    ∃ y, IsPeriodicPoint f M y ∧ f y ≠ 0 ∧ omegaLimitSet f M σ x = orbit f M y := by sorry

end TeschlODE.Planar
