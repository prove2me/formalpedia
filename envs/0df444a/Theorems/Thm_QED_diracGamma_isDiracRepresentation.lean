-- Prove2me | Theorems.Thm_QED_diracGamma_isDiracRepresentation
-- name    : QED.diracGamma_isDiracRepresentation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:10:53.462125+00:00
-- url     : https://prove2.me/theorems/d146d133-090d-4376-a26e-43d4eb7235f9
-- title:
--   The Dirac basis satisfies $\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_4$
-- statement:
--   The four explicit matrices of the standard Dirac basis form a Dirac representation: they satisfy the Clifford anticommutation relation
--   $$\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_4,\qquad \eta=\mathrm{diag}(1,-1,-1,-1),$$
--   for all $\mu,\nu\in\{0,1,2,3\}$, together with the hermiticity relation $(\gamma^\mu)^\dagger=\gamma^0\gamma^\mu\gamma^0$.
--
--   This is the existence statement that makes the abstract hypothesis used elsewhere in the mission non-vacuous: the Dirac matrices of the QED action are not merely postulated, a concrete family realizing them is exhibited. In particular $(\gamma^0)^2=I_4$ and $(\gamma^k)^2=-I_4$ for $k=1,2,3$, and distinct gamma matrices anticommute.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_fields

namespace QED
theorem diracGamma_isDiracRepresentation : IsDiracRepresentation diracGamma := by sorry
end QED
