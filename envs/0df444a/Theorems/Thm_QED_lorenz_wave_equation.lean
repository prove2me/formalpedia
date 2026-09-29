-- Prove2me | Theorems.Thm_QED_lorenz_wave_equation
-- name    : QED.lorenz_wave_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:22:22.222051+00:00
-- url     : https://prove2.me/theorems/1dda7e49-d220-431d-a061-22782cbdc2e0
-- title:
--   Lorenz gauge: $\Box A^\nu = e J^\nu$
-- statement:
--   Let $A$ be a $C^2$ four-potential satisfying the Maxwell equation $\partial_\mu F^{\mu\nu}=eJ^\nu$ and the Lorenz gauge condition $\eta^{\mu\nu}\partial_\mu A_\nu=0$. Then each raised component of the potential satisfies an inhomogeneous wave equation:
--   $$\Box A^\nu=e J^\nu,\qquad \Box=\eta^{\mu\nu}\partial_\mu\partial_\nu.$$
--
--   This is the QED version of the classical Maxwell equations in the Lorenz gauge. Substituting $F^{\mu\nu}=\partial^\mu A^\nu-\partial^\nu A^\mu$ into the equation of motion produces $\Box A^\nu-\partial^\nu(\partial_\mu A^\mu)$, and the gauge condition kills the second term. It is the form in which the four-potential propagates as a wave with the charge current as its source, and the form from which the photon propagator is read off.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem lorenz_wave_equation (e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (hA : ContDiff ℝ 2 A)
    (hM : IsMaxwellSolution e γ A ψ) (hL : LorenzGauge A) (ν : Fin 4) (x : Spacetime) :
    dAlembert (fun y => gaugeUp A ν y) x = e * current γ ψ ν x := by sorry
end QED
