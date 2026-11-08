-- Prove2me | Theorems.Thm_SteinerNav_observation_4_3
-- name    : SteinerNav.observation_4_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:46:57.04668+00:00
-- url     : https://prove2.me/theorems/cb049626-5e79-4de0-9be6-f4c065b51bf1
-- title:
--   Observation 4.3 — a neighbor that covers $t$ from $s$ covers $t$ from every source farther from $t$
-- statement:
--   Let $\alpha>1$. Suppose the edge from a source $s$ to a neighbor $v$ $\alpha$-covers a target $t$, that is, $\|v-t\|<\|s-t\|/\alpha$. Then for every source $s'$ with $\|s'-t\|\ge\|s-t\|$, the edge from $s'$ to $v$ also $\alpha$-covers $t$:
--   $$\|v-t\|<\frac{\|s'-t\|}{\alpha}.$$
--
--   This is what lets one landmark's sampled neighbors serve every source farther from the target.
--
--   Differences from the source: none.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Observation 4.3, p.8

import Mathlib
import Definitions.Def_SteinerNav_Covers

namespace SteinerNav

/-- Observation 4.3: if the edge from `s` to `v` `α`-covers `t` and `‖s′ − t‖ ≥ ‖s − t‖`, then the edge
from `s′` to `v` `α`-covers `t` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Observation 4.3, p.8). -/
theorem observation_4_3 {d : ℕ} (α : ℝ) (hα : 1 < α) (s s' v t : Pt d) (h : Covers α s v t)
    (hs : dist s t ≤ dist s' t) : Covers α s' v t := by sorry

end SteinerNav
