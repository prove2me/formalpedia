-- Prove2me | Theorems.Thm_ThirdLawThermo_boltzmannEntropy_one_eq_zero_and_pos
-- name    : ThirdLawThermo.boltzmannEntropy_one_eq_zero_and_pos
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:54.496974+00:00
-- url     : https://prove2.me/theorems/eb39c628-6e60-42ac-9004-99d6b9fed615
-- title:
--   $S=k_B\ln W$ vanishes for one microstate and is positive for more
-- statement:
--   Let $k_B>0$ be the Boltzmann constant and let $S_B(W)=k_B\ln W$ be the Boltzmann entropy of a macrostate with $W$ accessible microstates.
--
--   **Theorem.**
--
--   1. If only one microstate is accessible, the entropy vanishes: $S_B(1)=k_B\ln 1=0$.
--   2. If the number of accessible microstates is greater than one, the entropy is positive:
--   $$W>1\ \Longrightarrow\ S_B(W)=k_B\ln W>0 .$$
--
--   This is the statistical-mechanics reading of the third law used throughout the source: a system at absolute zero with a single accessible configuration has zero entropy, while at positive temperature several microstates are accessible and the entropy is positive.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "History" (statistical-mechanics definition of entropy, S = k_B ln Ω), and the figure caption in section "Explanation": "(a) Single possible configuration for a system at absolute zero, i.e., only one microstate is accessible. Thus S = k ln W = 0. (b) At temperatures greater than absolute zero, multiple microstates are accessible ... Since the number of accessible microstates is greater than 1, S = k ln W > 0."

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem boltzmannEntropy_one_eq_zero_and_pos (kB : ℝ) (hkB : 0 < kB) :
    boltzmannEntropy kB 1 = 0 ∧ ∀ W : ℕ, 1 < W → 0 < boltzmannEntropy kB W := by sorry

end ThirdLawThermo
