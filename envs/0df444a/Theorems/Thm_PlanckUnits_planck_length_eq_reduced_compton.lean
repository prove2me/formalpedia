-- Prove2me | Theorems.Thm_PlanckUnits_planck_length_eq_reduced_compton
-- name    : PlanckUnits.planck_length_eq_reduced_compton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:39:31.362898+00:00
-- url     : https://prove2.me/theorems/206e72fc-164d-4f61-afbc-2b6acb38b563
-- title:
--   The reduced Compton wavelength of the Planck mass is the Planck length
-- statement:
--   One of the standard interpretations of the Planck length (source: section *Analysis — Planck length*) is that it is the scale at which a particle's reduced Compton wavelength coincides with its Schwarzschild radius. This milestone records the first half: the reduced Compton wavelength $\hbar/(m_P c)$ of the Planck mass equals the Planck length $l_P$, for all positive $c,G,\hbar$.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem planck_length_eq_reduced_compton (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) :
    hbar / ((planckSystem c G hbar kB).mass * c) = (planckSystem c G hbar kB).length := by sorry

end PlanckUnits
