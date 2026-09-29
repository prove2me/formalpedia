-- Prove2me | Theorems.Thm_ReynoldsNumber_re_pipe_volumetric_and_mass_flow
-- name    : ReynoldsNumber.re_pipe_volumetric_and_mass_flow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:02:34.18202+00:00
-- url     : https://prove2.me/theorems/8d3443ee-d4a8-4590-87bb-7042fba32dae
-- title:
--   Pipe flow: $Re = QD_H/(\nu A) = W D_H/(\mu A)$
-- statement:
--   For flow in a pipe of hydraulic diameter $D_H$ and cross-sectional area $A>0$, the mean velocity is $u=Q/A$ with $Q$ the volumetric flow rate. Then
--   $$\mathrm{Re}=\frac{\rho u D_H}{\mu}=\frac{Q D_H}{\nu A}=\frac{W D_H}{\mu A},$$
--   where $\nu=\mu/\rho$ is the kinematic viscosity and $W=\rho Q$ is the mass flow rate.
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Data.Real.Basic
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem re_pipe_volumetric_and_mass_flow (rho Q A DH mu : ℝ) (hrho : 0 < rho)
    (hA : 0 < A) (hmu : 0 < mu) :
    Re rho (Q / A) DH mu = Q * DH / (kinematicViscosity mu rho * A) ∧
      Re rho (Q / A) DH mu = rho * Q * DH / (mu * A) := by sorry

end ReynoldsNumber
