-- Prove2me | Theorems.Thm_Penrose_poisson_equation
-- name    : Penrose.poisson_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:20:51.632434+00:00
-- url     : https://prove2.me/theorems/9a5d4409-a406-4a6a-a115-38252a77a26b
-- title:
--   Poisson's equation: $\nabla^2\Phi = -4\pi G\rho$
-- statement:
--   For every real gravitational constant $G$, every smooth, rapidly decreasing mass density $\rho$ on $\mathbb{R}^3$, and every point $x$, the Laplacian of the Newtonian potential $\Phi_\rho(x) = G\int \rho(y)/\|x-y\|\,dy$ satisfies
--
--   $$\nabla^2\Phi_\rho(x) = -4\pi G\,\rho(x).$$
--
--   This is Poisson's equation for the Newtonian gravitational potential, the first displayed formula in the chain of Section 6 of Penrose (1996, p. 595), stated here under the sign convention fixed by the mission ($\nabla^2\Phi = -4\pi G\rho$). The claim is pointwise, at every $x$ — including points carrying mass, where the potential kernel is singular — and requires no hypothesis beyond the smoothness and rapid decrease of $\rho$.
--
--   Solving Poisson's equation is how the difference $\nabla^2\Phi_\rho - \nabla^2\Phi_{\rho'} = -4\pi G(\rho - \rho')$ enters the computation of the incompatibility measure $\Delta$.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 595, Poisson's formula ∇²Φ = -4πGρ

import Mathlib
import Definitions.Def_penrose

open MeasureTheory

namespace Penrose

theorem poisson_equation (G : ℝ) (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian (newtonianPotential G ρ) x = -(4 * Real.pi) * G * ⇑ρ x := by sorry

end Penrose
