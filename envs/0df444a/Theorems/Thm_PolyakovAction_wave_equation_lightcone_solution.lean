-- Prove2me | Theorems.Thm_PolyakovAction_wave_equation_lightcone_solution
-- name    : PolyakovAction.wave_equation_lightcone_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T12:59:55.981891+00:00
-- url     : https://prove2.me/theorems/8ba9213d-c5da-457d-9a8b-30794a4cadd4
-- title:
--   Light-cone form of the general solution
-- statement:
--   Let $X:\mathbb R^2\to\mathbb R^D$ be $C^2$ and satisfy $\partial_\tau^2X^\mu-\partial_\sigma^2X^\mu=0$ everywhere (equivalently $\partial_+\partial_-X^\mu=0$ in light-cone coordinates $\xi^\pm=\tau\pm\sigma$). Then there are $C^2$ functions $X_+,X_-:\mathbb R\to\mathbb R^D$ with
--   $$X^\mu(\tau,\sigma)=X^\mu_+(\xi^+)+X^\mu_-(\xi^-)=X^\mu_+(\tau+\sigma)+X^\mu_-(\tau-\sigma).$$
--
--   This is the source's statement "the solution can be written as $X^\mu=X^\mu_+(\xi^+)+X^\mu_-(\xi^-)$".
--
--   **Formalization Note.** Stated on the whole plane $\mathbb R^2$; boundary conditions for closed/open strings are not part of this statement.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem wave_equation_lightcone_solution {D : ℕ} (X : Worldsheet → Spacetime D)
    (hX : ContDiff ℝ 2 X)
    (hwave : ∀ σ : Worldsheet, ∀ μ : Fin D,
      secondPartialDeriv X 0 0 μ σ - secondPartialDeriv X 1 1 μ σ = 0) :
    ∃ XL XR : ℝ → Spacetime D, ContDiff ℝ 2 XL ∧ ContDiff ℝ 2 XR ∧
      ∀ τ s : ℝ, X ![τ, s] = XL (τ + s) + XR (τ - s) := by sorry

end PolyakovAction
