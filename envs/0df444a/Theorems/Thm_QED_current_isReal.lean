-- Prove2me | Theorems.Thm_QED_current_isReal
-- name    : QED.current_isReal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:20:48.154532+00:00
-- url     : https://prove2.me/theorems/e40a1e48-75a4-4e55-ba05-c0958e31fae5
-- title:
--   Reality of the Dirac current $\bar\psi\gamma^\mu\psi$
-- statement:
--   For any family of Dirac matrices satisfying the Clifford and hermiticity relations, and any spinor field $\psi$, the quantity
--   $$\bar\psi\gamma^\mu\psi=\sum_{i,j}\overline{\psi_i}\,(\gamma^0\gamma^\mu)_{ij}\,\psi_j$$
--   is a real number at every point and for every index $\mu$: it equals its own real part.
--
--   Reality is a prerequisite for interpreting $J^\mu$ as an electric four-current and for the Maxwell equation $\partial_\mu F^{\mu\nu}=eJ^\nu$ to be an equation between real quantities. The proof is the hermiticity of the matrix $\gamma^0\gamma^\mu$, which follows from $(\gamma^\mu)^\dagger=\gamma^0\gamma^\mu\gamma^0$ and $(\gamma^0)^2=I_4$; no equation of motion and no regularity of $\psi$ is involved.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem current_isReal (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hγ : IsDiracRepresentation γ)
    (ψ : SpinorField) (μ : Fin 4) (x : Spacetime) :
    diracPairing γ (γ μ) (ψ x) (ψ x) = (current γ ψ μ x : ℂ) := by sorry
end QED
