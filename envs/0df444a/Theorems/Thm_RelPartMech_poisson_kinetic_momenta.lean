-- Prove2me | Theorems.Thm_RelPartMech_poisson_kinetic_momenta
-- name    : RelPartMech.poisson_kinetic_momenta
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:06:17.925983+00:00
-- url     : https://prove2.me/theorems/0ea2510b-700e-44cb-8b06-72f0fed1b6ee
-- title:
--   Poisson bracket of kinetic momenta is the force tensor
-- statement:
--   On phase space with canonical coordinates $(q^\alpha,p_\alpha)$ and Poisson bracket $\{f,h\}=\frac{\partial f}{\partial q^\mu}\frac{\partial h}{\partial p_\mu}-\frac{\partial f}{\partial p_\mu}\frac{\partial h}{\partial q^\mu}$, let $A_\alpha(x)$ be a smooth vector potential, $e$ a charge, and $\Pi_\alpha = p_\alpha - eA_\alpha(x)$ the kinetic momentum. Then
--
--   $$
--   \{\Pi_\alpha,\Pi_\beta\} = e\,F_{\alpha\beta},\qquad F_{\alpha\beta}=\partial_\alpha A_\beta-\partial_\beta A_\alpha .
--   $$
--
--   The force tensor thus appears as the Poisson bracket between kinetic momenta.
--
--   **Formalization Note** The source writes $q$ both for the charge and for the position coordinates; the charge is called $e$ here.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 3, eq. (8), last block

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem poisson_kinetic_momenta {n : ℕ} (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α))
    (e : ℝ) (α β : Fin n) (x p : Coord n) :
    poisson (kineticMomentum A e α) (kineticMomentum A e β) x p = e * forceTensor A α β x := by
  sorry

end RelPartMech
