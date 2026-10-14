-- Prove2me | Theorems.Thm_RelPartMech_poisson_position_fn_kinetic_momentum
-- name    : RelPartMech.poisson_position_fn_kinetic_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:06:59.672381+00:00
-- url     : https://prove2.me/theorems/f02f3df5-1b62-4341-81ec-1e0ea4c9ed4c
-- title:
--   Poisson bracket of a position function with kinetic momentum
-- statement:
--   For any smooth function $f(x^\alpha)$ of position only, and kinetic momentum $\Pi_\beta=p_\beta-eA_\beta(x)$,
--
--   $$
--   \{f(x^\alpha),\Pi_\beta\} = \partial_\beta f .
--   $$
--
--   In particular $\{x^\alpha,\Pi_\beta\}=\delta^\alpha_\beta$: kinetic momentum still generates translations of the position variables.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 3, eq. (8), third line

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem poisson_position_fn_kinetic_momentum {n : ℕ} (A : CovectorField n) (e : ℝ)
    (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f) (β : Fin n) (x p : Coord n) :
    poisson (fun y _ => f y) (kineticMomentum A e β) x p = pd β f x := by sorry

end RelPartMech
