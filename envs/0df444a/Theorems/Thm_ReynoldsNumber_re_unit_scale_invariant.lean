-- Prove2me | Theorems.Thm_ReynoldsNumber_re_unit_scale_invariant
-- name    : ReynoldsNumber.re_unit_scale_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:00:51.354844+00:00
-- url     : https://prove2.me/theorems/ba6f7b7c-df98-45b9-a71a-ceb5f3fc8d77
-- title:
--   Invariance of $Re$ under a change of the mass, length and time units
-- statement:
--   Rescaling the units of mass, length and time by positive factors $m$, $l$, $t$ multiplies the numerical value of a quantity of dimension $M^{\alpha}L^{\beta}T^{\gamma}$ by $m^{\alpha}l^{\beta}t^{\gamma}$. Applying this to $\rho\mapsto \rho m l^{-3}$, $u\mapsto u\,l\,t^{-1}$, $L\mapsto L\,l$ and $\mu\mapsto \mu\, m\, l^{-1}t^{-1}$, the Reynolds number is unchanged:
--   $$\mathrm{Re}\Bigl(\tfrac{\rho m}{l^{3}},\tfrac{u l}{t}, L l, \tfrac{\mu m}{l t}\Bigr)=\mathrm{Re}(\rho,u,L,\mu).$$
--   This is the precise sense in which $\mathrm{Re}$ is a dimensionless quantity: it is a pure number, independent of the system of units.
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Data.Real.Basic
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem re_unit_scale_invariant (m l t rho u L mu : ℝ) (hm : 0 < m) (hl : 0 < l)
    (ht : 0 < t) (hrho : 0 < rho) (hL : 0 < L) (hmu : 0 < mu) :
    Re (rho * m / l ^ 3) (u * l / t) (L * l) (mu * m / (l * t)) = Re rho u L mu := by sorry

end ReynoldsNumber
