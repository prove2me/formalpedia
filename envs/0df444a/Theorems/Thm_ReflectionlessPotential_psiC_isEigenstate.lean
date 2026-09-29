-- Prove2me | Theorems.Thm_ReflectionlessPotential_psiC_isEigenstate
-- name    : ReflectionlessPotential.psiC_isEigenstate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:48:43.122022+00:00
-- url     : https://prove2.me/theorems/20ed072a-f85e-4e90-8afb-4266c1b69ea4
-- title:
--   The continuum states $\psi_k$ are eigenstates of energy $k^2/2$
-- statement:
--   Equations (2.12) and (4.2): the normalized continuum eigenfunctions of the reflectionless potential.
--
--   For $\kappa > 0$ and any real $k$, the function
--   $$\psi_{k}(x) \;=\; \frac{e^{ikx}\bigl(k + i\kappa\tanh(\kappa x)\bigr)}{\sqrt{2\pi}\,(\kappa+ik)}$$
--   is twice differentiable and satisfies
--   $$-\tfrac12\,\psi_{k}''(x) \;-\; \kappa^{2}\operatorname{sech}^{2}(\kappa x)\,\psi_{k}(x) \;=\; \frac{k^{2}}{2}\,\psi_{k}(x)
--   \qquad \text{for all } x \in \mathbb{R},$$
--   so the spectrum of $H$ contains the whole positive half-line $E = k^{2}/2$, as it does for the free particle.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psiC_isEigenstate (κ k : ℝ) (hκ : 0 < κ) :
    IsEigenstate κ (k ^ 2 / 2) (psiC κ k) := by sorry

end ReflectionlessPotential
