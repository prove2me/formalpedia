-- Prove2me | Theorems.Thm_ReflectionlessPotential_creation_intertwines
-- name    : ReflectionlessPotential.creation_intertwines
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:47:13.626983+00:00
-- url     : https://prove2.me/theorems/d3d9811a-2be6-4783-90a3-068b617ad0d8
-- title:
--   $a^{\dagger}$ maps free eigenstates to eigenstates of $H$ at the same energy
-- statement:
--   Equation (2.11): the creation operator of the factorization method intertwines the free Hamiltonian with the reflectionless one.
--
--   In units $\hbar = m = 1$ put $a^{\dagger} = \tfrac{1}{\sqrt{2}}\bigl(P + i\kappa\tanh(\kappa X)\bigr)$ with $P = -i\,d/dx$, so that
--   $$\bigl(a^{\dagger}f\bigr)(x) \;=\; \frac{-i f'(x) + i\kappa\tanh(\kappa x)\,f(x)}{\sqrt{2}} .$$
--   If $f$ is a (not necessarily square-integrable) solution of the free Schrödinger equation $-\tfrac12 f'' = E f$ with derivative $f'$, then $a^{\dagger}f$ solves
--   $$-\tfrac12 (a^{\dagger}f)'' - \kappa^{2}\operatorname{sech}^{2}(\kappa x)\,(a^{\dagger}f) \;=\; E\,(a^{\dagger}f).$$
--   Applied to plane waves $f(x) = e^{ikx}$ with $E = k^{2}/2$, this is precisely how the paper produces the continuum states of the reflectionless potential out of free ones.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem creation_intertwines (κ E : ℝ) (hκ : 0 < κ) (f f' : ℝ → ℂ)
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : IsFreeEigenstate E f) :
    IsEigenstate κ E (creation κ f f') := by sorry

end ReflectionlessPotential
