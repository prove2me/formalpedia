-- Prove2me | Theorems.Thm_TegmarkDimensionality_hydrogen_energy_unbounded_below
-- name    : TegmarkDimensionality.hydrogen_energy_unbounded_below
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T03:06:28.916563+00:00
-- url     : https://prove2.me/theorems/ef30a3d1-f5db-4057-9997-9b3f6f5c1f59
-- title:
--   Hydrogen atom has no ground state for $n>3$
-- statement:
--   Let $n>3$ and $\kappa>0$, and if $n=4$ assume moreover $\kappa>1$. In units with $\hbar^2/2m=1$, the energy of a real state $\psi$ in the $n$-dimensional Coulomb potential $-\kappa|x|^{2-n}$ is
--   $$\mathcal E[\psi]=\int_{\mathbb R^n}|\nabla\psi(x)|^2\,dx-\kappa\int_{\mathbb R^n}|x|^{2-n}\,\psi(x)^2\,dx.$$
--   This energy is unbounded below. For every $E\in\mathbb R$ there is a smooth, compactly supported $\psi$ with $\int\psi^2=1$ and
--   $$\mathcal E[\psi]<E.$$
--
--   So the $n$-dimensional hydrogen atom has no ground state, but states of arbitrarily negative energy.
--
--   **Formalization Note** For $n\ge5$ the claim holds for every $\kappa>0$. For $n=4$ the potential scales like the kinetic term, and by Hardy's inequality $\int|\nabla\psi|^2\ge\int\psi^2/|x|^2$ the energy is bounded below when $\kappa\le1$. The four-dimensional case is therefore stated only for supercritical coupling $\kappa>1$. This qualification is not in the paper.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L71, first paragraph ('the hydrogen atom has no bound states for n > 3 ... no ground state, but time-dependent states of arbitrarily negative energy'), citing Tangherlini 1963

import Mathlib
open MeasureTheory
open scoped ContDiff

namespace TegmarkDimensionality

/-- For `n > 3` space dimensions, the hydrogen-like Schrödinger energy
`E[ψ] = ∫ |∇ψ|² - κ ∫ |x|^{2-n} ψ²` (Coulomb potential `-κ |x|^{2-n}` of `ℝⁿ`, units with
`ħ²/2m = 1`) is unbounded below on normalized smooth compactly supported states; for
`n = 4` this is asserted for supercritical coupling `κ > 1`. -/
theorem hydrogen_energy_unbounded_below (n : ℕ) (hn : 3 < n) (κ : ℝ) (hκ : 0 < κ)
    (hκ4 : n = 4 → 1 < κ) (E : ℝ) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∫ x, ψ x ^ 2) = 1 ∧
        (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) - κ * (∫ x, ‖x‖ ^ ((2 : ℝ) - n) * ψ x ^ 2) < E := by sorry

end TegmarkDimensionality
