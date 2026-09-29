-- Prove2me | Theorems.Thm_PlanckUnits_schwarzschild_radius_planck_mass
-- name    : PlanckUnits.schwarzschild_radius_planck_mass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:39:56.753896+00:00
-- url     : https://prove2.me/theorems/2a2175df-76b0-4151-81a8-3405218ce079
-- title:
--   The Schwarzschild radius of the Planck mass is $2\,l_P$
-- statement:
--   The second half of the heuristic identifying the Planck scale (source: section *Analysis — Planck length*): the Schwarzschild radius $2Gm_P/c^{2}$ of a body of one Planck mass equals twice the Planck length, for all positive $c$, $G$, $\hbar$. Together with the Compton-wavelength milestone this makes precise the statement that at the Planck mass the two length scales agree up to a factor $2$.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem schwarzschild_radius_planck_mass (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) :
    2 * G * (planckSystem c G hbar kB).mass / c ^ 2 =
      2 * (planckSystem c G hbar kB).length := by sorry

end PlanckUnits
