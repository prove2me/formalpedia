-- Prove2me | Theorems.Thm_QED_qed_field_equations
-- name    : QED.qed_field_equations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:22:47.343325+00:00
-- url     : https://prove2.me/theorems/422448be-5542-40da-9304-7d561a02e116
-- title:
--   Classical QED field equations: $\Box A^\nu=eJ^\nu$ with $\partial_\nu J^\nu=0$
-- statement:
--   **Goal theorem.** Let $\gamma$ be a family of Dirac matrices, let $m$ and $e$ be real, and let $(\psi,A)$ be a coupled solution of the classical QED field equations: $\psi$ is $C^1$ and satisfies the Dirac equation $(i\gamma^\mu D_\mu-m)\psi=0$, $A$ is $C^2$ and satisfies the Maxwell equation $\partial_\mu F^{\mu\nu}=eJ^\nu$ with $J^\mu=\bar\psi\gamma^\mu\psi$, and $A$ is in the Lorenz gauge $\eta^{\mu\nu}\partial_\mu A_\nu=0$. Then
--   $$\Box A^\nu = e\,J^\nu\qquad\text{for every }\nu,\qquad\text{and}\qquad \partial_\nu J^\nu = 0,$$
--   at every point of Minkowski space.
--
--   The two conclusions are the end point of the classical analysis of the QED action. The first is the wave equation obeyed by the electromagnetic four-potential in the Lorenz gauge, with the Dirac current as its source; the second is the conservation of that source, which is the consistency condition for the first — applying $\partial_\nu$ to $\partial_\mu F^{\mu\nu}$ gives zero identically, so no non-conserved current can appear on the right-hand side. Together they say that the coupled Dirac–Maxwell system of classical electrodynamics with a spin-$1/2$ source is a wave equation driven by a conserved charge current. Nothing quantized is asserted: this is the classical field theory that the perturbative expansion of QED quantizes.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem qed_field_equations (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hγ : IsDiracRepresentation γ) (A : GaugeField) (ψ : SpinorField)
    (hA : ContDiff ℝ 2 A) (hψ : ContDiff ℝ 1 ψ)
    (hD : IsDiracSolution m e γ A ψ) (hM : IsMaxwellSolution e γ A ψ)
    (hL : LorenzGauge A) :
    (∀ (ν : Fin 4) (x : Spacetime),
        dAlembert (fun y => gaugeUp A ν y) x = e * current γ ψ ν x) ∧
      (∀ x : Spacetime, (∑ ν : Fin 4, partialD ν (fun y => current γ ψ ν y) x) = 0) := by sorry
end QED
