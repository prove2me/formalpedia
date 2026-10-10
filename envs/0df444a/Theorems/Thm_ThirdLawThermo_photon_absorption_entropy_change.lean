-- Prove2me | Theorems.Thm_ThirdLawThermo_photon_absorption_entropy_change
-- name    : ThirdLawThermo.photon_absorption_entropy_change
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:22.186807+00:00
-- url     : https://prove2.me/theorems/c7098fe3-6d8e-4f5a-bed1-b438062713e5
-- title:
--   Crystal absorbing a photon: $\Delta S = k_B\ln N$
-- statement:
--   Consider a crystal lattice of $N$ identical atoms at $T=0$ which absorbs a single photon. Before absorption only one microstate is accessible; after absorption exactly one atom is excited and any of the $N$ atoms may be the excited one, so $N$ microstates are accessible. With the Boltzmann entropy $S_B(W)=k_B\ln W$:
--
--   **Theorem.** The entropy change caused by the absorption is
--   $$\Delta S=S_B(N)-S_B(1)=k_B\ln N .$$
--
--   This is the worked example of the source showing that the entropy of a crystal at absolute zero rises from $0$ when energy is absorbed.
--
--   **Formalization Note** The identity is stated for every natural number $N$ and every real $k_B$; for $N=0$ both sides are $0$ by the convention $\ln 0=0$.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "Example: Entropy change of a crystal lattice heated by an incoming photon" ("Initially, there is only one accessible microstate"; "after absorption, there are N possible microstates accessible by the system"; "The entropy change is [formula]"; the displayed formulas appear as images in the supplied PDF and are transcribed as ΔS = k_B ln N − k_B ln 1 from the surrounding text).

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem photon_absorption_entropy_change (kB : ℝ) (N : ℕ) :
    boltzmannEntropy kB N - boltzmannEntropy kB 1 = kB * Real.log N := by sorry

end ThirdLawThermo
