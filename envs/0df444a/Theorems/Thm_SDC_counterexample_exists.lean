-- Prove2me | Theorems.Thm_SDC_counterexample_exists
-- name    : SDC.counterexample_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-23T09:26:27.23973+00:00
-- url     : https://prove2.me/theorems/4826511a-0ce8-49c1-9476-21f453733b9f
-- title:
--   A finite counterexample to Sidorenko conjecture (the manuscript's main theorem)
-- statement:
--   The main theorem of the source manuscript, stated verbatim: a finite counterexample to Sidorenko conjecture. There is a positive size and a host graph on that many labelled vertices, with at least one edge, such that the homomorphism density of the 22-triple incidence pattern in the host is strictly below the 66th power of the host edge density. Sidorenko conjecture predicts the opposite inequality for every bipartite pattern and every host; this is the goal statement of the mission.
-- source:
--   Uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt), namespace OAI.SidorenkoCounterexample: the main theorem is stated verbatim from the manuscript, re-namespaced to SDC.

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  The main theorem of the source manuscript, stated verbatim (as the
manuscript main theorem): a finite counterexample to Sidorenko
conjecture. There is a positive size and a host graph on that many
labelled vertices, with at least one edge, such that the homomorphism
density of the 22-triple incidence pattern in the host is strictly below
the 66th power of the host edge density. Sidorenko conjecture predicts
the opposite inequality for every bipartite pattern and every host; this
is the goal statement of the mission.  -/

theorem counterexample_exists :
    ∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
      (∃ left right, host.Adj left right) ∧
      homDensity H host < (edgeDensity host) ^ 66 := by
  sorry

end SDC
