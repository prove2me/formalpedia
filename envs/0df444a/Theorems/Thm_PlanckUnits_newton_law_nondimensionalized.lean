-- Prove2me | Theorems.Thm_PlanckUnits_newton_law_nondimensionalized
-- name    : PlanckUnits.newton_law_nondimensionalized
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:40:54.928627+00:00
-- url     : https://prove2.me/theorems/9d98e7be-b970-49ec-bc7e-3c4200e7a53c
-- title:
--   Newton's law of gravitation in nondimensionalized form: $F'=m_1'm_2'/r'^{2}$
-- statement:
--   The source's opening example of nondimensionalization: Newton's law $F=Gm_1m_2/r^{2}$ is *equivalent* to the constant-free relation $F'=m_1'm_2'/r'^{2}$, where each primed symbol is the ratio of the corresponding quantity to its Planck unit — $F'=F/F_P$ with $F_P=c^{4}/G$, $m_i'=m_i/m_P$ and $r'=r/l_P$. The equivalence is stated for arbitrary real masses $m_1,m_2$ and force $F$ and for positive separation $r$.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem newton_law_nondimensionalized (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (m₁ m₂ r F : ℝ) (hr : 0 < r) :
    F = G * m₁ * m₂ / r ^ 2 ↔
      F / (c ^ 4 / G) =
        (m₁ / (planckSystem c G hbar kB).mass) * (m₂ / (planckSystem c G hbar kB).mass) /
          (r / (planckSystem c G hbar kB).length) ^ 2 := by sorry

end PlanckUnits
