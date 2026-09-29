-- Prove2me | Theorems.Thm_ReflectionlessPotential_bound_state_unique
-- name    : ReflectionlessPotential.bound_state_unique
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T19:59:05.437164+00:00
-- url     : https://prove2.me/theorems/18e3c725-bcc3-4f41-afa7-9d5f9e496b4f
-- title:
--   There is exactly one bound state, of energy $-\kappa^2/2$
-- statement:
--   §6 of the paper: the reflectionless potential ($N=1$) supports **exactly one** bound state.
--
--   Let $\kappa>0$ and let $f$ be a nonzero, square-integrable solution of
--   $$-\tfrac12 f''(x) - \kappa^{2}\operatorname{sech}^{2}(\kappa x) f(x) \;=\; E f(x)$$
--   with $E<0$. Then necessarily
--   $$E \;=\; -\frac{\kappa^{2}}{2}, \qquad f \;=\; c\,\psi_{0} \quad\text{for some } c\in\mathbb{C},$$
--   where $\psi_{0}(x) = \sqrt{\kappa/2}\,\operatorname{sech}(\kappa x)$. In other words the negative spectrum is the single simple eigenvalue $-\kappa^{2}/2$, which is the spectral counterpart of the paper's counting argument: the completeness defect has unit trace, hence exactly one bound state.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem bound_state_unique (κ E : ℝ) (hκ : 0 < κ) (hE : E < 0) (f : ℝ → ℂ)
    (hf : IsEigenstate κ E f) (hL2 : MemLp f 2 (volume : Measure ℝ)) (hne : f ≠ 0) :
    E = -(κ ^ 2 / 2) ∧ ∃ c : ℂ, ∀ x, f x = c * psi0 κ x := by sorry

end ReflectionlessPotential
