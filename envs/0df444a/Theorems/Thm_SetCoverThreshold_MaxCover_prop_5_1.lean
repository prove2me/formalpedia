-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_prop_5_1
-- name    : SetCoverThreshold.MaxCover.prop_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:07:32.029985+00:00
-- url     : https://prove2.me/theorems/01d304e0-73db-49b7-a689-382dde9e505f
-- title:
--   Proposition 5.1 — greedy covers at least (1 − 1/e)·opt
-- statement:
--   Let an instance of max $k$-cover be given and let $S_{j_1},\dots,S_{j_k}$ be selected greedily: each $S_{j_t}$ covers at least as many points outside $S_{j_1}\cup\dots\cup S_{j_{t-1}}$ as any other set of the instance (ties broken arbitrarily). Then
--   $$\Big|\bigcup_{t=1}^k S_{j_t}\Big|\ \ge\ \Big(1-\frac1e\Big)\,\mathrm{opt},$$
--   where $\mathrm{opt}$ is the largest number of points covered by $k$ sets.
--
--   This is the upper half of the threshold: together with Theorem 5.3 it shows that $1-1/e$ is the best ratio achievable in polynomial time unless $\mathrm{P}=\mathrm{NP}$.
--
--   **Formalization Note** The statement holds for every greedy run, whatever the tie-breaking. The polynomial running time of the greedy algorithm is not part of the statement.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), pp. 647–648, Proposition 5.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Instance

namespace SetCoverThreshold.MaxCover

/-- **Proposition 5.1** (Feige 1998, p. 647): every greedy run on a max k-cover instance covers
at least `(1 − 1/e) · opt` points. -/
theorem prop_5_1 (I : Instance) (run : Fin I.k → Fin I.sets.length) (hrun : IsGreedyRun I run) :
    (1 - Real.exp (-1)) * (opt I : ℝ) ≤ (coverOf I (Finset.univ.image run)).card := by sorry

end SetCoverThreshold.MaxCover
