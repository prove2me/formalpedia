-- Prove2me | Theorems.Thm_TeschlODE_Planar_periodic_of_omegaLimitSet_inter_halfOrbit
-- name    : TeschlODE.Planar.periodic_of_omegaLimitSet_inter_halfOrbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T15:33:17.685684+00:00
-- url     : https://prove2.me/theorems/05646eae-488d-4365-921f-c6629df5b98c
-- title:
--   Corollary 7.11 — ω_σ(x) ∩ γ_σ(x) ≠ ∅ implies x periodic
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open, $f \in C^1(M, \mathbb{R}^2)$, $x \in M$ and $\sigma \in \{\pm\}$. If $\omega_\sigma(x) \cap \gamma_\sigma(x) \neq \emptyset$, then $x$ is periodic and hence
--   $$\omega_+(x) = \omega_-(x) = \gamma(x).$$
--
--   **Formalization Note.** "Periodic" includes fixed points (period zero), as in the book's proof ("If $y$ is fixed … there is nothing to do").
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 222, Corollary 7.11

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_halfOrbit
import Definitions.Def_TeschlODE_Planar_omegaLimitSet
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint

namespace TeschlODE.Planar

/-- Teschl, Corollary 7.11 (p. 222): for `M ⊆ ℝ²` open, `f ∈ C¹(M, ℝ²)`, `x ∈ M` and `σ ∈ {±}`,
if `ω_σ(x) ∩ γ_σ(x) ≠ ∅` then `x` is periodic (possibly a fixed point) and
`ω₊(x) = ω₋(x) = γ(x)`. -/
theorem periodic_of_omegaLimitSet_inter_halfOrbit {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {x : Fin 2 → ℝ} (hx : x ∈ M)
    (h : (omegaLimitSet f M σ x ∩ halfOrbit f M σ x).Nonempty) :
    IsPeriodicPoint f M x ∧ omegaLimitSet f M true x = orbit f M x ∧
      omegaLimitSet f M false x = orbit f M x := by sorry

end TeschlODE.Planar
