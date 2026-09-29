-- Prove2me | Theorems.Thm_QED_lagrangian_gauge_invariant
-- name    : QED.lagrangian_gauge_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:17:52.600493+00:00
-- url     : https://prove2.me/theorems/5426ecb8-4ef5-4775-a460-4e5ea5bca10d
-- title:
--   $U(1)$ invariance of the QED Lagrangian density $\mathcal{L}$
-- statement:
--   The QED Lagrangian density
--   $$\mathcal{L}=\bar\psi\,(i\gamma^\mu D_\mu-m)\,\psi-\tfrac14F_{\mu\nu}F^{\mu\nu}$$
--   is invariant, pointwise in spacetime, under the $U(1)$ gauge transformation $A_\mu\mapsto A_\mu+\partial_\mu\chi$, $\psi\mapsto e^{-ie\chi}\psi$ with real parameter $\chi$.
--
--   This is the symmetry principle on which the whole theory is built: the statement that QED is an abelian gauge theory with group $U(1)$ is precisely the invariance of its action density under this transformation. The matter part is invariant because the phase cancels between $\bar\psi$ and the covariantly transforming $D_\mu\psi$, the mass term because $|e^{-ie\chi}|=1$, and the field part because the curvature is unchanged. By Noether's theorem this symmetry is what yields the conserved current $J^\mu=\bar\psi\gamma^\mu\psi$.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem lagrangian_gauge_invariant (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (χ : Spacetime → ℝ)
    (hA : ContDiff ℝ 1 A) (hχ : ContDiff ℝ 2 χ) (hψ : ContDiff ℝ 1 ψ) (x : Spacetime) :
    lagrangian m e γ (gaugeShift χ A) (gaugePhase e χ ψ) x = lagrangian m e γ A ψ x := by sorry
end QED
