-- Prove2me | Theorems.Thm_PlanckUnits_derived_planck_units
-- name    : PlanckUnits.derived_planck_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:40:18.309059+00:00
-- url     : https://prove2.me/theorems/09ee4980-7894-4227-8ad5-a2872db770e0
-- title:
--   Table 2: the coherent derived Planck units, and $k_B T_P = m_P c^{2}$
-- statement:
--   The coherent derived units of Table 2 of the source, in closed form: the Planck energy $m_Pc^{2}=\sqrt{\hbar c^{5}/G}$, the Planck momentum $m_Pc=\sqrt{\hbar c^{3}/G}$, the Planck force $m_Pc^{2}/l_P=c^{4}/G$, the Planck density $m_P/l_P^{3}=c^{5}/(\hbar G^{2})$, the Planck acceleration $l_P/t_P^{2}=\sqrt{c^{7}/(\hbar G)}$ and the Planck frequency $1/t_P=\sqrt{c^{5}/(\hbar G)}$; together with the energy–temperature relation $k_BT_P=m_Pc^{2}$ that makes the Planck temperature the temperature whose thermal energy is the Planck energy.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem derived_planck_units (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) (hk : 0 < kB) :
    (planckSystem c G hbar kB).mass * c ^ 2 = Real.sqrt (hbar * c ^ 5 / G) ∧
    (planckSystem c G hbar kB).mass * c = Real.sqrt (hbar * c ^ 3 / G) ∧
    (planckSystem c G hbar kB).mass * c ^ 2 / (planckSystem c G hbar kB).length = c ^ 4 / G ∧
    (planckSystem c G hbar kB).mass / (planckSystem c G hbar kB).length ^ 3 =
      c ^ 5 / (hbar * G ^ 2) ∧
    (planckSystem c G hbar kB).length / (planckSystem c G hbar kB).time ^ 2 =
      Real.sqrt (c ^ 7 / (hbar * G)) ∧
    1 / (planckSystem c G hbar kB).time = Real.sqrt (c ^ 5 / (hbar * G)) ∧
    kB * (planckSystem c G hbar kB).temperature = (planckSystem c G hbar kB).mass * c ^ 2 := by sorry

end PlanckUnits
