-- Prove2me | Theorems.Thm_PlanckUnits_planck_units_existence_and_uniqueness
-- name    : PlanckUnits.planck_units_existence_and_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:41:41.316187+00:00
-- url     : https://prove2.me/theorems/43abe6b0-caba-4917-acbd-4b8a049f28bb
-- title:
--   Planck units: existence and uniqueness of the $c=G=\hbar=k_B=1$ normalization
-- statement:
--   **Goal theorem.** Fix arbitrary positive values $c$, $G$, $\hbar$, $k_B$ for the speed of light, the gravitational constant, the reduced Planck constant and the Boltzmann constant. Then there is exactly one system of base units — one positive length, mass, time and temperature — in which all four constants have numerical value $1$, and it is the Planck system
--
--   $$l_P=\sqrt{\frac{\hbar G}{c^{3}}},\qquad m_P=\sqrt{\frac{\hbar c}{G}},\qquad t_P=\sqrt{\frac{\hbar G}{c^{5}}},\qquad T_P=\frac{1}{k_B}\sqrt{\frac{\hbar c^{5}}{G}}.$$
--
--   The statement combines existence (the Planck system is positive and normalizes the four constants) with uniqueness (any positive normalizing system equals it). It is the precise form of the claim, made throughout the literature on natural units, that "setting $c=G=\hbar=k_B=1$" determines a system of units completely.
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem planck_units_existence_and_uniqueness (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hk : 0 < kB) :
    (planckSystem c G hbar kB).IsPositive ∧
      (planckSystem c G hbar kB).Normalizes c G hbar kB ∧
      ∀ u : UnitSystem, u.IsPositive → u.Normalizes c G hbar kB →
        u = planckSystem c G hbar kB := by sorry

end PlanckUnits
