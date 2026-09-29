-- Prove2me | Theorems.Thm_PlanckUnits_planck_system_unique_of_normalizes
-- name    : PlanckUnits.planck_system_unique_of_normalizes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:38:24.755281+00:00
-- url     : https://prove2.me/theorems/d29a7e18-f03b-468d-9b55-20335f86dd3f
-- title:
--   Uniqueness: a positive unit system normalizing $c,G,\hbar,k_B$ is the Planck system
-- statement:
--   For arbitrary positive constants $c$, $G$, $\hbar$, $k_B$: if a system of base units with strictly positive length, mass, time and temperature makes all four constants numerically equal to $1$, then its four base units are exactly the Planck length, Planck mass, Planck time and Planck temperature. This is the uniqueness half of the mission's goal — the statement that gives the Planck units their claim to be *the* natural units attached to $c$, $G$, $\hbar$, $k_B$.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem planck_system_unique_of_normalizes (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hk : 0 < kB) (u : UnitSystem) (hu : u.IsPositive) (hn : u.Normalizes c G hbar kB) :
    u = planckSystem c G hbar kB := by sorry

end PlanckUnits
