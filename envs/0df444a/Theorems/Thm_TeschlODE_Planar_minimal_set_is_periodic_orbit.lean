-- Prove2me | Theorems.Thm_TeschlODE_Planar_minimal_set_is_periodic_orbit
-- name    : TeschlODE.Planar.minimal_set_is_periodic_orbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T15:37:19.404799+00:00
-- url     : https://prove2.me/theorems/ff11de5f-6795-42bd-85c2-ea5f23a83edc
-- title:
--   Corollary 7.12 — a minimal compact σ invariant set is a periodic orbit
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ be open and $f \in C^1(M, \mathbb{R}^2)$. A nonempty, compact, $\sigma$ invariant set $C \subseteq M$ is **minimal** if it contains no proper $\sigma$ invariant subset that is nonempty and compact (p. 195). Every minimal compact $\sigma$ invariant set is a periodic orbit:
--   $$C = \gamma(x) \quad\text{for some periodic point } x \in C.$$
--
--   In dimension three and higher this fails (orbits can be dense on an invariant torus), so the corollary isolates what is special about the plane.
--
--   **Formalization Note.** $\sigma$ invariance is written out as $\gamma_\sigma(x) \subseteq C$ for all $x \in C$ (6.17); minimality as: every nonempty compact $\sigma$ invariant $D \subseteq C$ equals $C$. A fixed orbit (period zero) counts as a periodic orbit.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 222, Corollary 7.12 (minimal sets: p. 195)

import Mathlib
import Definitions.Def_TeschlODE_Planar_orbit
import Definitions.Def_TeschlODE_Planar_halfOrbit
import Definitions.Def_TeschlODE_Planar_IsPeriodicPoint

namespace TeschlODE.Planar

/-- Teschl, Corollary 7.12 (p. 222), with the definition of a minimal set from p. 195: let
`M ⊆ ℝ²` be open and `f ∈ C¹(M, ℝ²)`. Let `C ⊆ M` be a minimal compact `σ` invariant set, i.e.
`C` is nonempty, compact and `σ` invariant (`γ_σ(x) ⊆ C` for `x ∈ C`, (6.17)), and every nonempty
compact `σ` invariant subset of `C` equals `C`. Then `C` is a periodic orbit: `C = γ(x)` for a
periodic point `x ∈ C` (a fixed point, of period zero, is allowed). -/
theorem minimal_set_is_periodic_orbit {M : Set (Fin 2 → ℝ)} (hM : IsOpen M)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiffOn ℝ 1 f M) (σ : Bool)
    {C : Set (Fin 2 → ℝ)} (hCM : C ⊆ M) (hCne : C.Nonempty) (hCc : IsCompact C)
    (hCinv : ∀ x ∈ C, halfOrbit f M σ x ⊆ C)
    (hCmin : ∀ D ⊆ C, D.Nonempty → IsCompact D → (∀ x ∈ D, halfOrbit f M σ x ⊆ D) → D = C) :
    ∃ x ∈ C, IsPeriodicPoint f M x ∧ C = orbit f M x := by sorry

end TeschlODE.Planar
