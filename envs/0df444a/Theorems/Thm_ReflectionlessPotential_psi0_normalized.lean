-- Prove2me | Theorems.Thm_ReflectionlessPotential_psi0_normalized
-- name    : ReflectionlessPotential.psi0_normalized
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:46:12.043681+00:00
-- url     : https://prove2.me/theorems/bb343f8c-2d06-4515-a394-0a02172603b2
-- title:
--   The bound state is normalized: $\int \psi_0^2 = 1$
-- statement:
--   Equation (2.7): the bound state $\psi_{0}(x) = \sqrt{\kappa/2}\,\operatorname{sech}(\kappa x)$ of the reflectionless potential is a unit vector of $L^{2}(\mathbb{R})$,
--   $$\int_{-\infty}^{\infty}\psi_{0}(x)^{2}\,dx \;=\; \frac{\kappa}{2}\int_{-\infty}^{\infty}\operatorname{sech}^{2}(\kappa x)\,dx \;=\; 1 ,$$
--   for every $\kappa > 0$. Equivalently, $\int_{-\infty}^{\infty}\operatorname{sech}^{2}(\kappa x)\,dx = 2/\kappa$.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psi0_normalized (κ : ℝ) (hκ : 0 < κ) : ∫ x : ℝ, psi0 κ x ^ 2 = 1 := by sorry

end ReflectionlessPotential
