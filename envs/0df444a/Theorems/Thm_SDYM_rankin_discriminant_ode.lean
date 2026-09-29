-- Prove2me | Theorems.Thm_SDYM_rankin_discriminant_ode
-- name    : SDYM.rankin_discriminant_ode
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-21T01:51:43.310973+00:00
-- url     : https://prove2.me/theorems/305bc88f-11e5-4db4-b4fa-cb0091d86689
-- title:
--   Rankin's fourth-order homogeneous equation for the discriminant $\Delta$
-- statement:
--   The Chazy equation written in Hirota (tau-function) form. The source records that the particular Chazy solution can be written as a logarithmic potential,
--
--   $$y(t) = \frac{1}{2}\frac{d}{dt}\log\Delta(t),$$
--
--   where $\Delta$ is the discriminant cusp form of weight $12$, and that $\Delta$ therefore satisfies the homogeneous fourth-degree equation first obtained by Rankin:
--
--   $$\Delta^3\frac{d^4\Delta}{dt^4} - 5\Delta^2\frac{d\Delta}{dt}\frac{d^3\Delta}{dt^3} - \frac{3}{2}\Delta^2\left(\frac{d^2\Delta}{dt^2}\right)^2 + 12\Delta\left(\frac{d\Delta}{dt}\right)^2\frac{d^2\Delta}{dt^2} - \frac{13}{2}\left(\frac{d\Delta}{dt}\right)^4 = 0 .$$
--
--   Since $\Delta$ has no zeros or poles and satisfies a homogeneous equation, it is the natural analogue of the tau function of Hirota's method; the Fourier coefficients of $\Delta$ are the Ramanujan $\tau$-function.
--
--   The statement is the general implication: any nonvanishing four-times-differentiable $\Delta$ whose logarithmic derivative halved solves the Chazy equation satisfies Rankin's equation. No modularity is assumed or used.
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.A p. 3169, Eqs. (74), (76) and the displayed homogeneous ODE of degree 4 attributed to Rankin

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem rankin_discriminant_ode
    (s : Set ℂ) (D D₁ D₂ D₃ D₄ y₁ y₂ : ℂ → ℂ)
    (hD : ∀ t ∈ s, HasDerivAt D (D₁ t) t)
    (hD₁ : ∀ t ∈ s, HasDerivAt D₁ (D₂ t) t)
    (hD₂ : ∀ t ∈ s, HasDerivAt D₂ (D₃ t) t)
    (hD₃ : ∀ t ∈ s, HasDerivAt D₃ (D₄ t) t)
    (hDne : ∀ t ∈ s, D t ≠ 0)
    (hchazy : IsChazySolution s (fun z => D₁ z / (2 * D z)) y₁ y₂) :
    ∀ t ∈ s, D t ^ 3 * D₄ t - 5 * D t ^ 2 * D₁ t * D₃ t
      - 3 / 2 * D t ^ 2 * D₂ t ^ 2 + 12 * D t * D₁ t ^ 2 * D₂ t
      - 13 / 2 * D₁ t ^ 4 = 0 := by sorry

end SDYM
