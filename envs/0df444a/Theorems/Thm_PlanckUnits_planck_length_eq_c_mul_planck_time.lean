-- Prove2me | Theorems.Thm_PlanckUnits_planck_length_eq_c_mul_planck_time
-- name    : PlanckUnits.planck_length_eq_c_mul_planck_time
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:38:46.977985+00:00
-- url     : https://prove2.me/theorems/6b8542b8-ac6a-49bf-b9ee-f8f60598602d
-- title:
--   Consistency of Table 1: $l_P = c\,t_P$
-- statement:
--   The Planck length is the distance light travels in one Planck time: with $l_P=\sqrt{\hbar G/c^{3}}$ and $t_P=\sqrt{\hbar G/c^{5}}$ one has $l_P=c\,t_P$, for all positive $c$, $G$, $\hbar$. Equivalently, the speed of light has numerical value $1$ in Planck units, which is the first of the four defining normalizations.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem planck_length_eq_c_mul_planck_time (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) :
    (planckSystem c G hbar kB).length = c * (planckSystem c G hbar kB).time := by sorry

end PlanckUnits
