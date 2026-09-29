-- Prove2me | Theorems.Thm_QED_fieldStrength_bianchi
-- name    : QED.fieldStrength_bianchi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:11:37.562201+00:00
-- url     : https://prove2.me/theorems/3dc6e9ec-3641-4dda-9ab1-1a5259025cbb
-- title:
--   Bianchi identity $\partial_\lambda F_{\mu\nu}+\partial_\mu F_{\nu\lambda}+\partial_\nu F_{\lambda\mu}=0$
-- statement:
--   For a twice continuously differentiable four-potential $A$, the field tensor $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu$ satisfies the Bianchi identity
--   $$\partial_\lambda F_{\mu\nu}+\partial_\mu F_{\nu\lambda}+\partial_\nu F_{\lambda\mu}=0$$
--   at every point and for every triple of indices $\lambda,\mu,\nu$, not assumed distinct.
--
--   This is the homogeneous half of Maxwell's equations — in three-dimensional language, the absence of magnetic charge and Faraday's law. It is an identity, not an equation of motion: it holds for *every* potential, with no reference to the current, the coupling or the spinor field, and it expresses the fact that $F$ is the curvature of a connection. The only analytic input is the symmetry of second derivatives, which is where the $C^2$ hypothesis is used.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem fieldStrength_bianchi (A : GaugeField) (hA : ContDiff ℝ 2 A)
    (lam μ ν : Fin 4) (x : Spacetime) :
    partialD lam (fun y => fieldStrength A μ ν y) x
      + partialD μ (fun y => fieldStrength A ν lam y) x
      + partialD ν (fun y => fieldStrength A lam μ y) x = 0 := by sorry
end QED
