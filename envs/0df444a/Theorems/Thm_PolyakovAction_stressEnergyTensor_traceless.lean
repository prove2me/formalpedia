-- Prove2me | Theorems.Thm_PolyakovAction_stressEnergyTensor_traceless
-- name    : PolyakovAction.stressEnergyTensor_traceless
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:15:39.651908+00:00
-- url     : https://prove2.me/theorems/9c2caf18-ca4c-458a-b6d7-2c5a2463a383
-- title:
--   The stress–energy tensor is traceless
-- statement:
--   Let $h_{ab}(\sigma)$ be symmetric with $\det h_{ab}(\sigma)\neq0$. Then the stress–energy tensor $T_{ab}=T\big(G_{ab}-\tfrac12h_{ab}h^{cd}G_{cd}\big)$ is traceless at $\sigma$:
--   $$T^a{}_a=h^{ab}T_{ab}=0.$$
--
--   In the source this is the consequence of Weyl symmetry: since the action does not depend on the conformal factor $\phi$, $\delta S/\delta\phi=0$ forces $T^a{}_a=0$.
--
--   **Formalization Note.** The trace is computed directly from the explicit formula for $T_{ab}$ (which the source derives from $\delta S/\delta h^{ab}$); it is a pointwise statement.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem stressEnergyTensor_traceless {D : ℕ} (T : ℝ)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) (hsymm : (h σ)ᵀ = h σ) (hdet : (h σ).det ≠ 0) :
    ∑ a, ∑ b, (h σ)⁻¹ a b * stressEnergyTensor T g h X σ a b = 0 := by sorry

end PolyakovAction
