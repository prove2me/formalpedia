-- Prove2me | Theorems.Thm_ReflectionlessPotential_psi0_isEigenstate
-- name    : ReflectionlessPotential.psi0_isEigenstate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:46:46.474983+00:00
-- url     : https://prove2.me/theorems/230e5ca8-f76c-4a51-a5a8-5a5c49f5f3d1
-- title:
--   The bound state has energy $E_0 = -\kappa^2/2$
-- statement:
--   Equation (2.1) with (2.7): the ground state solves the Schrödinger equation of the reflectionless potential with energy $E_{0} = -\kappa^{2}/2$ (that is, $-\hbar^{2}\kappa^{2}/2m$ in physical units).
--
--   Explicitly, for $\kappa>0$ the function $\psi_{0}(x) = \sqrt{\kappa/2}\,\operatorname{sech}(\kappa x)$ is twice differentiable and satisfies
--   $$-\tfrac12\,\psi_{0}''(x) \;-\; \kappa^{2}\operatorname{sech}^{2}(\kappa x)\,\psi_{0}(x)
--   \;=\; -\frac{\kappa^{2}}{2}\,\psi_{0}(x) \qquad\text{for all } x \in \mathbb{R}.$$
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psi0_isEigenstate (κ : ℝ) (hκ : 0 < κ) :
    IsEigenstate κ (-(κ ^ 2 / 2)) (fun x => (psi0 κ x : ℂ)) := by sorry

end ReflectionlessPotential
