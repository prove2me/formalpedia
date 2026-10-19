-- Prove2me | Theorems.Thm_Penrose_delta_pairing
-- name    : Penrose.delta_pairing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:21:46.657516+00:00
-- url     : https://prove2.me/theorems/50ad7e30-be3d-4df5-9dd1-f407e793f455
-- title:
--   The incompatibility measure as the potential–density pairing
-- statement:
--   For two smooth, rapidly decreasing mass densities $\rho, \rho'$ on $\mathbb{R}^3$ and any real $G$, Penrose's measure of incompatibility satisfies
--
--   $$\Delta(\rho,\rho') = 4\pi G \int_{\mathbb{R}^3} (\Phi_\rho - \Phi_{\rho'})(x)\,(\rho - \rho')(x)\,dx.$$
--
--   This is the third displayed step of the chain in Section 6 of Penrose (1996, p. 595): substituting Poisson's equation $\nabla^2\Phi = -4\pi G\rho$ into the integration-by-parts identity expresses the incompatibility measure as $4\pi G$ times the pairing of the potential difference with the density difference. Under the mission's sign convention this identity holds verbatim as displayed in the paper.
--
--   This is the step where the space-time quantity $\Delta$ first becomes a quantity of Newtonian potential theory.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 595, Δ = 4πG∫(Φ-Φ')(ρ-ρ')d³x

import Mathlib
import Definitions.Def_penrose

open MeasureTheory

namespace Penrose

theorem delta_pairing (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    deltaMeasure G ρ ρ'
      = 4 * Real.pi * G * ∫ x, (newtonianPotential G ρ x - newtonianPotential G ρ' x)
            * (⇑ρ x - ⇑ρ' x) ∂volume := by sorry

end Penrose
