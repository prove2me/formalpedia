-- Prove2me | Theorems.Thm_QED_fieldStrength_gauge_invariant
-- name    : QED.fieldStrength_gauge_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:15:21.944068+00:00
-- url     : https://prove2.me/theorems/3f8ac0fd-03cb-4a94-8a03-fbb6236dca60
-- title:
--   Gauge invariance of the field tensor: $F_{\mu\nu}[A+d\chi]=F_{\mu\nu}[A]$
-- statement:
--   For a $C^1$ four-potential $A$ and a $C^2$ real scalar $\chi$, the field tensor is unchanged by the gauge transformation $A_\mu\mapsto A_\mu+\partial_\mu\chi$:
--   $$F_{\mu\nu}[A+d\chi](x)=F_{\mu\nu}[A](x)$$
--   for all indices $\mu,\nu$ and all points $x$.
--
--   This is the statement that the physically meaningful object built from the potential is the curvature, not the potential itself: the $U(1)$ gauge freedom of electrodynamics acts on $A$ but leaves $F$ — and hence the electric and magnetic fields — fixed. It is the field-strength half of the gauge invariance of the QED action.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem fieldStrength_gauge_invariant (A : GaugeField) (χ : Spacetime → ℝ)
    (hA : ContDiff ℝ 1 A) (hχ : ContDiff ℝ 2 χ) (μ ν : Fin 4) (x : Spacetime) :
    fieldStrength (gaugeShift χ A) μ ν x = fieldStrength A μ ν x := by sorry
end QED
