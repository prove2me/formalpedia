-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_task_checked_P9_000_2
-- name    : RealPinwheel.FiveSixths.task_checked_P9_000_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:34.50034+00:00
-- url     : https://prove2.me/theorems/a4c65386-bce9-4e8c-8342-c134c4b79b37
-- title:
--   Task arithmetic P9_000 group 3
-- statement:
--   For every word in witness block P9_000, the three tasks numbered 7 through 9 satisfy their exact endpoint, mean, prefix-count, and discrepancy conditions.
--
--   $$\operatorname{TaskChecked}(w,i).$$
--
--   These finite integer conditions are the corresponding task coordinates of the full all-window witness check. They are separated to keep verification of long source words within individual compilation bounds.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family P9, entries 1–1, task coordinates 7–9.

import Definitions.Def_RealPinwheel_FiveSixths_TaskWitnessCheck
import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_000
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.task_checked_P9_000_2 (j : Fin 1) (i : Fin 3) : taskWitnessCheck (witnessP9_000 j) (⟨6 + i.val, by omega⟩ : Fin 9) = true := by sorry
