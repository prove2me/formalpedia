-- Prove2me | Theorems.Thm_ResistantSets_remark_2_8
-- name    : ResistantSets.remark_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:06.129122+00:00
-- url     : https://prove2.me/theorems/0bbb0a53-97ab-4c20-bc7e-a2e25a25fd65
-- title:
--   Remark 2.8 — $R_{k,1}$ ($k\ge1$) and $R_5$ are resistant
-- statement:
--   For every $k\ge1$ the set $R_{k,1}$ is resistant, and $R_5$ is resistant.
--
--   Together with the fact that these sets are half-dense and strictly non-polar, this gives the "these sets qualify" half of Theorem 1.17.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Remark 2.8, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5

namespace ResistantSets

/-- **Remark 2.8** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.11): "{R_{k,1} : k ≥ 1} ∪ {R5} are resistant sets." -/
theorem remark_2_8 : (∀ k : ℕ, 1 ≤ k → IsResistant (Rk1 k)) ∧ IsResistant R5 := by sorry

end ResistantSets
