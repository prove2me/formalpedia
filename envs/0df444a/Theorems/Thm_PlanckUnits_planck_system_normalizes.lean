-- Prove2me | Theorems.Thm_PlanckUnits_planck_system_normalizes
-- name    : PlanckUnits.planck_system_normalizes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:33:19.603426+00:00
-- url     : https://prove2.me/theorems/24c2bca0-9119-4d84-84d4-4a270123cc26
-- title:
--   Table 1: the Planck units are positive and normalize $c$, $G$, $\hbar$, $k_B$
-- statement:
--   For arbitrary positive constants $c$, $G$, $\hbar$, $k_B$, the Planck system of Table 1 consists of four positive units, and in it each of the four constants has numerical value $1$: $l_P/t_P=c$, $l_P^{3}/(m_P t_P^{2})=G$, $m_P l_P^{2}/t_P=\hbar$ and $m_P l_P^{2}/(t_P^{2}T_P)=k_B$. This is the existence half of the mission's goal, and it also shows the normalization conditions are satisfiable, so that the uniqueness milestone is not vacuous.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem planck_system_normalizes (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hk : 0 < kB) :
    (planckSystem c G hbar kB).IsPositive ∧
      (planckSystem c G hbar kB).Normalizes c G hbar kB := by sorry

end PlanckUnits
