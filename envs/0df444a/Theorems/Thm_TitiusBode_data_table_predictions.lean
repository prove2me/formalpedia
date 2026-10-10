-- Prove2me | Theorems.Thm_TitiusBode_data_table_predictions
-- name    : TitiusBode.data_table_predictions
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:45.785982+00:00
-- url     : https://prove2.me/theorems/02b4c7a6-b69f-4682-aa90-0e2f1326d3fa
-- title:
--   Data table — the predicted Titius–Bode distances
-- statement:
--   The Titius–Bode distances $a(n) = 0.4 + 0.3\cdot 2^n$ (au) are, for $n = -\infty, 0, 1, \dots, 8$:
--
--   $$
--   0.4,\; 0.7,\; 1.0,\; 1.6,\; 2.8,\; 5.2,\; 10.0,\; 19.6,\; 38.8,\; 77.2 .
--   $$
--
--   The first nine values form the "T–B rule distance" column of the data table of the source (Mercury, Venus, Earth, Mars, Ceres, Jupiter, Saturn, Uranus, Pluto); the values $10.0, 19.6, 38.8, 77.2$ for $n = 5, \dots, 8$ are the "about $10, 20, 39$ and $77$ au" quoted for Saturn, Uranus, Neptune and Pluto in the section "Original formulation".
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Data" (table, column "T–B rule distance (AU)") and section "Original formulation"

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem data_table_predictions :
    tbAU ⊥ = 0.4 ∧ tbAU ((0 : ℕ) : WithBot ℕ) = 0.7 ∧ tbAU ((1 : ℕ) : WithBot ℕ) = 1.0 ∧
    tbAU ((2 : ℕ) : WithBot ℕ) = 1.6 ∧ tbAU ((3 : ℕ) : WithBot ℕ) = 2.8 ∧
    tbAU ((4 : ℕ) : WithBot ℕ) = 5.2 ∧ tbAU ((5 : ℕ) : WithBot ℕ) = 10.0 ∧
    tbAU ((6 : ℕ) : WithBot ℕ) = 19.6 ∧ tbAU ((7 : ℕ) : WithBot ℕ) = 38.8 ∧
    tbAU ((8 : ℕ) : WithBot ℕ) = 77.2 := by sorry
end TitiusBode
