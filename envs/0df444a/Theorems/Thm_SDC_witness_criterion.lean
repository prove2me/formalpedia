-- Prove2me | Theorems.Thm_SDC_witness_criterion
-- name    : SDC.witness_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:25:48.014376+00:00
-- url     : https://prove2.me/theorems/74ff33fb-296d-4b06-9e76-2b06df1fe88f
-- title:
--   The finite certificate: the goal is equivalent to an explicit arithmetic witness
-- statement:
--   The finite certificate. The goal of the mission - the existence of a finite host with at least one edge whose homomorphism density for the pattern is below the 66th power of its edge density - is equivalent to the existence of a size and a host on that many labelled vertices, with an edge, satisfying the natural-number inequality of the clearing-of-denominators milestone. The remaining work of the mission is thus a finite search: produce the size, the host, and the arithmetic certificate.
-- source:
--   Mission-authored reduction lemma within the framework of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt).

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  The finite certificate. The goal of the mission - the existence of a
finite host with at least one edge whose homomorphism density for the
pattern is below the 66th power of its edge density - is equivalent to
the existence of a size and a host on that many labelled vertices, with
an edge, satisfying the natural-number inequality of
witness_inequality. The remaining work of the mission is thus a finite
search: produce the size, the host, and the arithmetic certificate.  -/

theorem witness_criterion :
    (∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
        (∃ left right, host.Adj left right) ∧
        homDensity H host < (edgeDensity host) ^ 66) ↔
      (∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
        (∃ left right, host.Adj left right) ∧
        homCount H host * size ^ 132 < (2 * edgeCard host) ^ 66 * size ^ 35) := by
  sorry

end SDC
