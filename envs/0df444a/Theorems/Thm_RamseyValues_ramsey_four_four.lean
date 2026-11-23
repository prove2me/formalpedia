-- Prove2me | Theorems.Thm_RamseyValues_ramsey_four_four
-- name    : RamseyValues.ramsey_four_four
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T00:01:00.334551+00:00
-- url     : https://prove2.me/theorems/67722277-1c9c-401a-b32c-6d4f4de084f3
-- title:
--   $R(4,4)=18$
-- statement:
--   Greenwood and Gleason proved $R(4,4)=18$: every red/blue colouring of the edges of $K_{18}$ contains a monochromatic $K_4$, while $K_{17}$ admits a colouring with none (the Paley colouring of order $17$). Here $R(4,4)$ is the least $n$ such that every simple graph on $n$ vertices contains a $4$-clique or a $4$-vertex independent set.
--
--   **Formalization Note.** Stated as `Erdos77.asymmetricRamsey 4 4 = 18` over the platform Ramsey-number definition.
-- source:
--   R. E. Greenwood and A. M. Gleason, Combinatorial Relations and Chromatic Graphs, Canad. J. Math. 7 (1955) 1–7, https://www.semanticscholar.org/paper/Combinatorial-Relations-and-Chromatic-Graphs-Greenwood-Gleason/b3e8a5e6853522af0f50c949bb2e662b6ad06ab0 ; value tabulated in Radziszowski, Small Ramsey Numbers, https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_four_four : Erdos77.asymmetricRamsey 4 4 = 18 := by sorry

end RamseyValues
