-- Prove2me | Theorems.Thm_Penrose_delta_laplacian
-- name    : Penrose.delta_laplacian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:21:19.374202+00:00
-- url     : https://prove2.me/theorems/402e839e-ddc4-4950-ba2d-30ccf849cf19
-- title:
--   Integration by parts: $\Delta = -\int(\Phi-\Phi')(\nabla^2\Phi-\nabla^2\Phi')$
-- statement:
--   For two smooth, rapidly decreasing mass densities $\rho, \rho'$ on $\mathbb{R}^3$ and any real $G$, Penrose's measure of incompatibility
--
--   $$\Delta(\rho,\rho') = \int_{\mathbb{R}^3} \|\nabla\Phi_\rho - \nabla\Phi_{\rho'}\|^2\,dx$$
--
--   satisfies the whole-space integration-by-parts identity
--
--   $$\Delta(\rho,\rho') = -\int_{\mathbb{R}^3} (\Phi_\rho - \Phi_{\rho'})(x)\,\bigl(\nabla^2\Phi_\rho - \nabla^2\Phi_{\rho'}\bigr)(x)\,dx.$$
--
--   This is the second displayed step of the chain in Section 6 of Penrose (1996, p. 595). The boundary terms at infinity vanish because the difference potential and its gradient decay; for a difference distribution with nonzero total mass the difference potential decays only like $1/\|x\|$, so the decay is a genuine estimate, not an assumption.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 595, second displayed chain identity Δ = -∫(Φ-Φ')(∇²Φ-∇²Φ')d³x

import Mathlib
import Definitions.Def_penrose

open MeasureTheory

namespace Penrose

theorem delta_laplacian (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    deltaMeasure G ρ ρ'
      = -∫ x, (newtonianPotential G ρ x - newtonianPotential G ρ' x)
            * laplacian (fun y => newtonianPotential G ρ y - newtonianPotential G ρ' y) x
          ∂volume := by sorry

end Penrose
