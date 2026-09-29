-- Prove2me | Theorems.Thm_ReynoldsNumber_viscous_coefficient_eq_inv_Re
-- name    : ReynoldsNumber.viscous_coefficient_eq_inv_Re
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:29:42.92088+00:00
-- url     : https://prove2.me/theorems/cd874d72-a5bc-449c-974d-16572d06b665
-- title:
--   Nondimensionalised Navier–Stokes: the viscous coefficient is $\mu/(\rho L V)=1/Re$
-- statement:
--   When the incompressible Navier–Stokes equations for a Newtonian fluid are rendered nondimensional using the mean velocity $V$, the characteristic length $L$ and the density $\rho$, the viscous term acquires the coefficient $\mu/(\rho L V)$. This coefficient is exactly the reciprocal of the Reynolds number:
--   $$\frac{\mu}{\rho L V}=\frac{1}{\mathrm{Re}(\rho,V,L,\mu)}.$$
--   It is in this sense that the nondimensional equations depend on the flow only through $\mathrm{Re}$.
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Data.Real.Basic
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem viscous_coefficient_eq_inv_Re (rho V L mu : ℝ) (hrho : 0 < rho) (hV : 0 < V)
    (hL : 0 < L) (hmu : 0 < mu) : mu / (rho * L * V) = 1 / Re rho V L mu := by sorry

end ReynoldsNumber
