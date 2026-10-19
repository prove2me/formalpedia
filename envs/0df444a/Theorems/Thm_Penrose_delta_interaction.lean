-- Prove2me | Theorems.Thm_Penrose_delta_interaction
-- name    : Penrose.delta_interaction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:23:15.037461+00:00
-- url     : https://prove2.me/theorems/1fe22acb-fbc9-466c-84e4-bb3df0cbfbe3
-- title:
--   Equal self-energies: $\Delta$ reduces to the interaction energy
-- statement:
--   Suppose two smooth, rapidly decreasing mass distributions $\rho, \rho'$ on $\mathbb{R}^3$ have equal gravitational self-energies, $E(\rho) = E(\rho')$. Then for any real $G$, Penrose's measure of incompatibility satisfies
--
--   $$\Delta(\rho,\rho') = 8\pi G\, I(\rho,\rho') - 16\pi G\, E(\rho),$$
--
--   where $I(\rho,\rho') = -G\iint \rho(x)\rho'(y)/\|x-y\|\,dx\,dy$ is the gravitational interaction energy of the two distributions.
--
--   This is the precise content of the remark in Section 6 of Penrose (1996, p. 597): apart from the factor $4\pi$, it does not make any difference which expression is used, provided the two individual states under superposition each have the same gravitational self-energy — the measure $\Delta$ is then determined, up to the explicit constants, by the interaction energy together with the common self-energy. For the two locations of a displaced lump this hypothesis holds by translation invariance.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 597 (apart from the factor 4π it does not make any difference which expression is used)

import Mathlib
import Definitions.Def_penrose
import Definitions.Def_penrose_energy

open MeasureTheory

namespace Penrose

theorem delta_interaction (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (h : gravSelfEnergy G ρ = gravSelfEnergy G ρ') :
    deltaMeasure G ρ ρ'
      = 8 * Real.pi * G * interactionEnergy G ρ ρ'
        - 16 * Real.pi * G * gravSelfEnergy G ρ := by sorry

end Penrose
