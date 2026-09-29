-- Prove2me | Theorems.Thm_ReflectionlessPotential_completeness_relation
-- name    : ReflectionlessPotential.completeness_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T20:00:06.715799+00:00
-- url     : https://prove2.me/theorems/9169aece-4ca0-4718-87d8-d8d42d646b97
-- title:
--   Completeness of the eigenfunctions of the reflectionless potential
-- statement:
--   **Completeness of the energy eigenfunctions of the reflectionless potential** (equation (3.5) of the paper, combined with (4.9) and (6.1)), stated in Parseval form.
--
--   Fix $\kappa > 0$ and work in units $\hbar = m = 1$, so that the Hamiltonian is
--   $$H = -\tfrac12\frac{d^{2}}{dx^{2}} - \kappa^{2}\operatorname{sech}^{2}(\kappa x).$$
--   Its normalized bound state and its normalized continuum states are
--   $$\psi_{0}(x) = \sqrt{\tfrac{\kappa}{2}}\,\operatorname{sech}(\kappa x), \qquad
--   \psi_{k}(x) = \frac{e^{ikx}\,\bigl(k + i\kappa\tanh \kappa x\bigr)}{\sqrt{2\pi}\,(\kappa + ik)}
--   \quad (k \in \mathbb{R}).$$
--
--   For a continuous, compactly supported $f : \mathbb{R} \to \mathbb{C}$ write the expansion coefficients
--   $$\langle \psi_{k}, f\rangle = \int_{-\infty}^{\infty}\overline{\psi_{k}(x)}\,f(x)\,dx,
--   \qquad
--   \langle \psi_{0}, f\rangle = \int_{-\infty}^{\infty}\psi_{0}(x)\,f(x)\,dx .$$
--
--   The theorem asserts that the continuum states together with the single bound state exhaust the norm of $f$:
--   $$\int_{-\infty}^{\infty}\bigl|\langle\psi_{k},f\rangle\bigr|^{2}\,dk
--   \;+\; \bigl|\langle\psi_{0},f\rangle\bigr|^{2}
--   \;=\;\int_{-\infty}^{\infty}\lvert f(x)\rvert^{2}\,dx .$$
--
--   This is the rigorous, distribution-free content of the completeness relation
--   $\sum_{n}\overline{\psi_{n}(x)}\psi_{n}(y) + \int \overline{\psi_{k}(x)}\psi_{k}(y)\,dk = \delta(x-y)$:
--   the continuum alone is not complete, and the deficit is exactly the rank-one contribution of $\psi_{0}$.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem completeness_relation (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    (∫ k : ℝ, ‖coeffC κ k f‖ ^ 2) + ‖coeff0 κ f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by sorry

end ReflectionlessPotential
