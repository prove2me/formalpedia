-- Prove2me | Theorems.Thm_ReflectionlessPotential_psi0_hasDerivAt
-- name    : ReflectionlessPotential.psi0_hasDerivAt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:45:44.783053+00:00
-- url     : https://prove2.me/theorems/d1a91243-d9af-491b-98b0-f148c2e58016
-- title:
--   The ground state is annihilated by $a$: $\psi_0' = -\kappa\tanh(\kappa x)\,\psi_0$
-- statement:
--   Equation (2.6)–(2.7) of the paper: the ground state is the solution of the first-order equation $a\psi_{0} = 0$.
--
--   With $\psi_{0}(x) = \sqrt{\kappa/2}\,\operatorname{sech}(\kappa x)$ and $\kappa > 0$, the claim is that $\psi_0$ is differentiable at every real $x$ with
--   $$\psi_{0}'(x) \;=\; -\kappa\,\tanh(\kappa x)\,\psi_{0}(x),$$
--   which is precisely the statement that $\psi_0$ is annihilated by the lowering operator $a = \tfrac{1}{\sqrt{2}}\bigl(P - i\kappa\tanh(\kappa X)\bigr)$, $P = -i\,d/dx$.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psi0_hasDerivAt (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    HasDerivAt (psi0 κ) (-(κ * Real.tanh (κ * x)) * psi0 κ x) x := by sorry

end ReflectionlessPotential
