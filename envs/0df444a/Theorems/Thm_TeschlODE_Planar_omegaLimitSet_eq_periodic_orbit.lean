-- Prove2me | Theorems.Thm_TeschlODE_Planar_omegaLimitSet_eq_periodic_orbit
-- name    : TeschlODE.Planar.omegaLimitSet_eq_periodic_orbit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:45:01.362988+00:00
-- url     : https://prove2.me/theorems/aeb20c4c-43bf-47a2-b73a-b7acd7b24582
-- title:
--   Lemma 7.14 — a connected ω_σ(x) containing a regular periodic orbit equals it
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $x \in M$ and $\sigma \in \{\pm\}$. Suppose $\omega_\sigma(x)$ is connected and contains a regular periodic orbit $\gamma(y)$. Then
--   $$\omega_\sigma(x) = \gamma(y).$$
--
--   **Formalization Note.** "Connected" is `IsPreconnected` (nonemptiness is automatic, since $\gamma(y) \subseteq \omega_\sigma(x)$). "Regular periodic orbit $\gamma(y)$" is: $y$ periodic, $f(y) \neq 0$, and $\gamma(y) \subseteq \omega_\sigma(x)$. No compactness is assumed, as in the book.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 222, Lemma 7.14

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint

namespace TeschlODE.Planar

/-- Teschl, Lemma 7.14 (p. 222): for `M ⊆ ℝ²` open, `f ∈ C¹(M, ℝ²)`, `x ∈ M` and `σ ∈ {±}`, if
`ω_σ(x)` is connected and contains a regular periodic orbit `γ(y)` (`y` periodic, `f y ≠ 0`,
`γ(y) ⊆ ω_σ(x)`), then `ω_σ(x) = γ(y)`. -/
theorem omegaLimitSet_eq_periodic_orbit {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    (hconn : IsPreconnected (omegaLimitSet f M σ x))
    {y : Fin 2 → ℝ} (hy : IsPeriodicPoint f M y) (hyreg : f y ≠ 0)
    (hsub : orbit f M y ⊆ omegaLimitSet f M σ x) :
    omegaLimitSet f M σ x = orbit f M y := by sorry

end TeschlODE.Planar
