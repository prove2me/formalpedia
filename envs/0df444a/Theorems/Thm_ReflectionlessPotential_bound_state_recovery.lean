-- Prove2me | Theorems.Thm_ReflectionlessPotential_bound_state_recovery
-- name    : ReflectionlessPotential.bound_state_recovery
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:59:37.194985+00:00
-- url     : https://prove2.me/theorems/5598652a-515d-4e1c-954e-0816f94e60cf
-- title:
--   The bound state is recovered, up to a phase, from the continuum defect
-- statement:
--   §6, equation (6.1): the bound state wave function can be read off from the knowledge of the continuum eigenstates alone.
--
--   The continuum states miss completeness by exactly the kernel $\frac{\kappa}{2\cosh\kappa x \cosh \kappa y}$, which therefore has to equal $\overline{\psi_{0}(x)}\psi_{0}(y)$. This determines $\psi_{0}$ up to an overall phase: if $g : \mathbb{R}\to\mathbb{C}$ satisfies
--   $$\overline{g(x)}\,g(y) \;=\; \frac{\kappa}{2\cosh\kappa x\,\cosh\kappa y}\qquad\text{for all }x,y,$$
--   then there is a unimodular constant $c$ with $g(x) = c\,\psi_{0}(x) = c\sqrt{\kappa/2}\operatorname{sech}(\kappa x)$ for all $x$. This is the elementary version of the inverse bound-state problem discussed at the end of the paper.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem bound_state_recovery (κ : ℝ) (hκ : 0 < κ) (g : ℝ → ℂ)
    (hg : ∀ x y : ℝ, (starRingEnd ℂ) (g x) * g y =
      ((κ / (2 * Real.cosh (κ * x) * Real.cosh (κ * y)) : ℝ) : ℂ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, g x = c * psi0 κ x := by sorry

end ReflectionlessPotential
