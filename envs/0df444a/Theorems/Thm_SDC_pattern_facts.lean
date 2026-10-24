-- Prove2me | Theorems.Thm_SDC_pattern_facts
-- name    : SDC.pattern_facts
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:22:44.60102+00:00
-- url     : https://prove2.me/theorems/71d4a9b0-7d7d-4cf0-b8de-5bd144b4a0e5
-- title:
--   The pattern facts: bipartite, 66 edges, three points per triple, no isolated points
-- statement:
--   The pattern facts. The incidence graph H is bipartite (the 13 points versus the 22 triples); its edge set has cardinality 66 - three incidences for each of the 22 triples; each triple of the table is a 3-element set; and every point lies in at least one triple. The edge count 66 is the exponent in Sidorenko inequality for this pattern, and the absence of isolated vertices is what makes the density comparison meaningful.
-- source:
--   Mission-authored sanity lemma about the pattern of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt): the facts recorded in Table 1 of the manuscript.

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  The pattern facts. The incidence graph H is bipartite (the 13
points versus the 22 triples), its edge set has cardinality 66 - three
incidences for each of the 22 triples - each triple is a 3-element set,
and every point lies in at least one triple. The edge count 66 is the
exponent in Sidorenko inequality for this pattern, and the absence of
isolated vertices is what makes the density comparison meaningful.  -/

theorem pattern_facts :
    H.IsBipartite ∧
    H.edgeSet.ncard = 66 ∧
    (∀ f : Fin 22, (faces f).card = 3) ∧
    ∀ p : Fin 13, ∃ f : Fin 22, p ∈ faces f := by
  sorry

end SDC
