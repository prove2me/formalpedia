-- Prove2me | Theorems.Thm_ReflectionlessPotential_fourier_poisson
-- name    : ReflectionlessPotential.fourier_poisson
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T19:51:42.062976+00:00
-- url     : https://prove2.me/theorems/a1570de9-2f85-4724-a160-585a2a4931e4
-- title:
--   $\int e^{ikt}/(k^2+\kappa^2)\,dk = (\pi/\kappa)e^{-\kappa|t|}$
-- statement:
--   Equation (4.5): the Green's function integral used to evaluate the continuum contribution to the completeness relation.
--
--   For $\kappa > 0$ and every real $t$,
--   $$\int_{-\infty}^{\infty}\frac{e^{ikt}}{k^{2}+\kappa^{2}}\,dk \;=\; \frac{\pi}{\kappa}\,e^{-\kappa\lvert t\rvert},$$
--   equivalently $\int_{-\infty}^{\infty}\frac{e^{ikt}}{k^{2}+\kappa^{2}}\frac{dk}{2\pi} = \frac{1}{2\kappa}e^{-\kappa\lvert t\rvert}$, which is the form quoted in the paper with $t = y-x$. The paper evaluates it by residues at the simple poles $k = \pm i\kappa$, closing the contour in the half plane selected by the sign of $t$.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem fourier_poisson (κ t : ℝ) (hκ : 0 < κ) :
    ∫ k : ℝ, Complex.exp (Complex.I * k * t) / ((k : ℂ) ^ 2 + (κ : ℂ) ^ 2) =
      ((Real.pi / κ * Real.exp (-(κ * |t|)) : ℝ) : ℂ) := by sorry

end ReflectionlessPotential
