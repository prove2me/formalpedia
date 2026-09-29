-- Prove2me | Theorems.Thm_PlanckUnits_rationalized_planck_system
-- name    : PlanckUnits.rationalized_planck_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:41:20.375271+00:00
-- url     : https://prove2.me/theorems/1d6b0e2c-b9af-4ff9-9ec5-704a0742ff6c
-- title:
--   Rationalized Planck units: normalizing $4\pi G$ in place of $G$
-- statement:
--   The source's *Alternative choices of normalization*: rationalized Planck units are defined by $c=4\pi G=\hbar=k_B=1$. This milestone states the corresponding uniqueness result — any positive system of base units in which $c$, $4\pi G$, $\hbar$ and $k_B$ all have numerical value $1$ has length $\sqrt{4\pi\hbar G/c^{3}}$, mass $\sqrt{\hbar c/(4\pi G)}$, time $\sqrt{4\pi\hbar G/c^{5}}$ and temperature $\sqrt{\hbar c^{5}/(4\pi G)}/k_B$, i.e. the Planck units rescaled by $\sqrt{4\pi}$ (mass by $1/\sqrt{4\pi}$).
-- source:
--   Planck units, Wikipedia, https://en.wikipedia.org/wiki/Planck_units (sections "Introduction", "History and definition" incl. Table 1, "Derived units" incl. Table 2, "Analysis", "Alternative choices of normalization"); original source of the units: Max Planck, "Über irreversible Strahlungsvorgänge", Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin 5 (1899), 440-480, pp. 478-480.

import Definitions.Def_planck_units

namespace PlanckUnits

theorem rationalized_planck_system (c G hbar kB : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar) (hk : 0 < kB)
    (u : UnitSystem) (hu : u.IsPositive) (hn : u.Normalizes c (4 * Real.pi * G) hbar kB) :
    u.length = Real.sqrt (4 * Real.pi * hbar * G / c ^ 3) ∧
    u.mass = Real.sqrt (hbar * c / (4 * Real.pi * G)) ∧
    u.time = Real.sqrt (4 * Real.pi * hbar * G / c ^ 5) ∧
    u.temperature = Real.sqrt (hbar * c ^ 5 / (4 * Real.pi * G)) / kB := by sorry

end PlanckUnits
