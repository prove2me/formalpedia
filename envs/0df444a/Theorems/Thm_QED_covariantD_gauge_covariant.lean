-- Prove2me | Theorems.Thm_QED_covariantD_gauge_covariant
-- name    : QED.covariantD_gauge_covariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:17:06.824635+00:00
-- url     : https://prove2.me/theorems/bc9d0ad2-519f-480f-a7ef-029482315907
-- title:
--   Covariance of $D_\mu$: $D_\mu(e^{-ie\chi}\psi)=e^{-ie\chi}D_\mu\psi$
-- statement:
--   Under the $U(1)$ gauge transformation $A_\mu\mapsto A_\mu+\partial_\mu\chi$, $\psi\mapsto e^{-ie\chi}\psi$ with real parameter $\chi$, the gauge covariant derivative $D_\mu\psi=\partial_\mu\psi+ieA_\mu\psi$ transforms in the same way as the field itself:
--   $$D_\mu\big(e^{-ie\chi}\psi\big)\big[A+d\chi\big]=e^{-ie\chi}\,D_\mu\psi[A].$$
--
--   This is the reason the derivative in the QED action is $D_\mu$ and not $\partial_\mu$: the ordinary derivative of $e^{-ie\chi}\psi$ picks up an extra term $-ie(\partial_\mu\chi)e^{-ie\chi}\psi$, and the shift of the potential is exactly what cancels it. Covariance of $D_\mu$ is what makes the matter part of the Lagrangian gauge invariant, and it is the sense in which $A_\mu$ is a connection.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem covariantD_gauge_covariant (e : ℝ) (A : GaugeField) (ψ : SpinorField)
    (χ : Spacetime → ℝ) (hχ : ContDiff ℝ 1 χ) (hψ : ContDiff ℝ 1 ψ)
    (μ : Fin 4) (x : Spacetime) :
    covariantD e (gaugeShift χ A) (gaugePhase e χ ψ) μ x
      = Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) • covariantD e A ψ μ x := by sorry
end QED
