-- Prove2me | Theorems.Thm_ReputationLies_Matching_topHeavy_strictConvexOn
-- name    : ReputationLies.Matching.topHeavy_strictConvexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:04.623397+00:00
-- url     : https://prove2.me/theorems/93b83752-65bc-4b28-925e-21afc5c03375
-- title:
--   §4.2, p. 15 (PDF 17) — a top-heavy market has a strictly convex F, a bottom-heavy market a strictly concave F
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   If the outside market is top-heavy (the density $f = F'$ is strictly increasing on $(0,1)$), then the CDF $F$ is strictly convex on $X = [0,1]$. If it is bottom-heavy ($f$ strictly decreasing on $(0,1)$), then $F$ is strictly concave on $[0,1]$.
--
--   This turns the shape of the outside market into risk attitudes: with a top-heavy market the hiring probability behaves like the expected utility of a risk lover, and with a bottom-heavy market like that of a risk-averse agent.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 15 (PDF 17), §4.2, paragraph after the Definition

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- §4.2, p. 15: a top-heavy market (strictly increasing density) has a strictly convex CDF `F` on
`X = [0, 1]`; a bottom-heavy market (strictly decreasing density) a strictly concave one. -/
theorem topHeavy_strictConvexOn (P : Primitives) (hP : P.Standing) :
    (P.TopHeavy → StrictConvexOn ℝ (Icc 0 1) P.F) ∧
    (P.BottomHeavy → StrictConcaveOn ℝ (Icc 0 1) P.F) := by sorry

end ReputationLies.Matching
