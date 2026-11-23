-- Prove2me | Theorems.Thm_RamseyValues_ramsey_five_five_le_49
-- name    : RamseyValues.ramsey_five_five_le_49
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T00:06:26.010347+00:00
-- url     : https://prove2.me/theorems/d36c590d-2b17-4224-bf30-97638cd7755e
-- title:
--   $R(5,5)\le 49$
-- statement:
--   McKay and Radziszowski proved the upper bound $R(5,5)\le 49$ by combining subgraph-counting identities with an exhaustive computer search over the possible $(5,5)$-graphs. Equivalently, every simple graph on $49$ vertices contains a $5$-clique or a $5$-vertex independent set. This was the first computational upper bound on $R(5,5)$ and the starting point of the modern upper-bound ladder.
--
--   **Formalization Note.** Stated as `Erdos77.asymmetricRamsey 5 5 ≤ 49` over the platform Ramsey-number definition.
-- source:
--   B. D. McKay and S. P. Radziszowski, Subgraph Counting Identities and Ramsey Numbers, J. Combin. Theory Ser. B 69 (1997) 193–209, https://www.sciencedirect.com/science/article/pii/S0095895696917414 (R(5,5) ≤ 49).

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_five_five_le_49 : Erdos77.asymmetricRamsey 5 5 ≤ 49 := by sorry

end RamseyValues
