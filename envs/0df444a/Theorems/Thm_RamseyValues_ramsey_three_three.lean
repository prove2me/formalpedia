-- Prove2me | Theorems.Thm_RamseyValues_ramsey_three_three
-- name    : RamseyValues.ramsey_three_three
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T23:58:51.541565+00:00
-- url     : https://prove2.me/theorems/86a27df0-9505-40e1-91a6-84e62fcb7e83
-- title:
--   $R(3,3)=6$
-- statement:
--   Greenwood and Gleason proved $R(3,3)=6$: every red/blue colouring of the edges of $K_6$ contains a monochromatic triangle, whereas $K_5$ admits a colouring with none (the pentagon colouring). Here $R(3,3)$ is the least $n$ such that every simple graph on $n$ vertices contains a $3$-clique or a $3$-vertex independent set. This is the first nontrivial diagonal Ramsey value and the base of the small-value ladder.
--
--   **Formalization Note.** Stated as `Erdos77.asymmetricRamsey 3 3 = 6` over the platform Ramsey-number definition.
-- source:
--   R. E. Greenwood and A. M. Gleason, Combinatorial Relations and Chromatic Graphs, Canad. J. Math. 7 (1955) 1–7, https://www.semanticscholar.org/paper/Combinatorial-Relations-and-Chromatic-Graphs-Greenwood-Gleason/b3e8a5e6853522af0f50c949bb2e662b6ad06ab0 ; value tabulated in Radziszowski, Small Ramsey Numbers, https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_three_three : Erdos77.asymmetricRamsey 3 3 = 6 := by sorry

end RamseyValues
