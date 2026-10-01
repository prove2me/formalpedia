-- Prove2me | Theorems.Thm_PolyakovAction_lorentz_invariance_first_order
-- name    : PolyakovAction.lorentz_invariance_first_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T09:40:28.0441+00:00
-- url     : https://prove2.me/theorems/e48f28f8-6ca5-4f12-bafe-60d57c6bfffe
-- title:
--   Invariance under infinitesimal Lorentz transformations
-- statement:
--   Let $g_{\mu\nu}$ be a constant symmetric target metric and $\omega^\mu{}_\nu$ a matrix with $\omega_{\mu\nu}=g_{\mu\lambda}\omega^\lambda{}_\nu=-\omega_{\nu\mu}$. Let $X$ be differentiable and assume the Polyakov densities of $X$ and of $\omega X$ are integrable over the region $U$. Then under $X^\alpha\to X^\alpha+\varepsilon\,\omega^\alpha{}_\beta X^\beta$,
--   $$S[X+\varepsilon\,\omega X]=S[X]+O(\varepsilon^2)\qquad(\varepsilon\to0).$$
--
--   This is transformation (ii) of the source's Poincaré symmetry: the action is invariant under infinitesimal Lorentz transformations, $\mathcal S'=\mathcal S+O(\omega^2)$.
--
--   **Formalization Note.** "Infinitesimal" is encoded by scaling a fixed generator $\omega$ by a real parameter $\varepsilon$ and asserting a big-$O(\varepsilon^2)$ bound as $\varepsilon\to0$. The integrability hypotheses express finiteness of the action, implicit in the source.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem lorentz_invariance_first_order {D : ℕ} (T : ℝ) (g : Matrix (Fin D) (Fin D) ℝ)
    (hg : gᵀ = g) (ω : Matrix (Fin D) (Fin D) ℝ) (hω : (g * ω)ᵀ = -(g * ω))
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (hX : Differentiable ℝ X) (U : Set Worldsheet)
    (hL : IntegrableOn (polyakovLagrangian (fun _ => g) h X) U)
    (hLω : IntegrableOn (polyakovLagrangian (fun _ => g) h (fun σ => ω *ᵥ X σ)) U) :
    (fun ε : ℝ => polyakovAction T (fun _ => g) h (fun σ => X σ + ε • (ω *ᵥ X σ)) U
        - polyakovAction T (fun _ => g) h X U) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by sorry

end PolyakovAction
