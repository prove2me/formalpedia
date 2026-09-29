-- Prove2me | Theorems.Thm_QED_current_conservation
-- name    : QED.current_conservation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:21:54.355218+00:00
-- url     : https://prove2.me/theorems/8cb0e241-e028-4964-94de-7f4294df3ad2
-- title:
--   Noether conservation law $\partial_\mu(\bar\psi\gamma^\mu\psi)=0$ for Dirac solutions
-- statement:
--   If a $C^1$ spinor field $\psi$ satisfies the Dirac equation $(i\gamma^\mu D_\mu-m)\psi=0$ in a four-potential $A$, with $\gamma$ a Dirac representation and $m$, $e$ real, then its current is conserved:
--   $$\partial_\mu J^\mu=0,\qquad J^\mu=\bar\psi\gamma^\mu\psi,$$
--   at every point of spacetime.
--
--   This is the Noether current of the $U(1)$ symmetry of the QED Lagrangian, and its conservation is what allows the Maxwell equation $\partial_\mu F^{\mu\nu}=eJ^\nu$ to have solutions at all: the left-hand side is annihilated by $\partial_\nu$ identically, so a non-conserved source would be inconsistent. Physically it is the conservation of electric charge. The proof combines the Dirac equation with its adjoint; the hermiticity relation $(\gamma^\mu)^\dagger=\gamma^0\gamma^\mu\gamma^0$ and the reality of $m$, $e$ and $A_\mu$ are exactly what make the terms containing $A_\mu$ cancel.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem current_conservation (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ) (A : GaugeField) (ψ : SpinorField)
    (hψ : ContDiff ℝ 1 ψ) (hD : IsDiracSolution m e γ A ψ) (x : Spacetime) :
    (∑ μ : Fin 4, partialD μ (fun y => current γ ψ μ y) x) = 0 := by sorry
end QED
