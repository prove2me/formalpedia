-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_task_checked_P9_000_1
-- name    : RealPinwheel.FiveSixths.task_checked_P9_000_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:54.399865+00:00
-- url     : https://prove2.me/theorems/f0193934-2161-4b20-acde-d8e6c6a3fe30
-- title:
--   Task arithmetic P9_000 group 2
-- statement:
--   For every word in witness block P9_000, the three tasks numbered 4 through 6 satisfy their exact endpoint, mean, prefix-count, and discrepancy conditions.
--
--   $$\operatorname{TaskChecked}(w,i).$$
--
--   These finite integer conditions are the corresponding task coordinates of the full all-window witness check. They are separated to keep verification of long source words within individual compilation bounds.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family P9, entries 1–1, task coordinates 4–6.

import Definitions.Def_RealPinwheel_FiveSixths_TaskWitnessCheck
import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_000
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.task_checked_P9_000_1 (j : Fin 1) (i : Fin 3) : taskWitnessCheck (witnessP9_000 j) (⟨3 + i.val, by omega⟩ : Fin 9) = true := by sorry
