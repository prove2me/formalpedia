-- Prove2me | Theorems.Thm_SensitivityGraphLocal_exists_215_success
-- name    : SensitivityGraphLocal.exists_215_success
-- status  : Open
-- author  : @dmilosch
-- created : 2026-11-06T18:57:13.348897+00:00
-- url     : https://prove2.me/theorems/ad20026e-0c5e-42d3-ae38-b22ed55a00da
-- title:
--   A sensitivity search with exact-sized graph checks reaches 2.15
-- statement:
--   Find raw finite graph-and-labeling data $D$, a positive state count $n+1$, and a depth $k$ for which
--
--   $$\operatorname{localSearch}(D,n+1,k)=\mathrm{true}.$$
--
--   The input must satisfy the original tournament, regularity, and parameter conditions, together with the absence of coherent, bounded-defect, and source configurations on subsets of exactly their forbidden cardinalities. The unchanged finite profile search must retain a profile of height $H$ satisfying
--
--   $$H^{43}<K^{20k}.$$
--
--   Here $K$ is the vertex count. This is the open witness-existence obligation after reducing graph validation to exact-sized subsets. No graph, labeling, numerical parameters, successful depth, or 2.15 separation is supplied or claimed to be known.
-- source:
--   Original hereditary-subset reduction of SensitivityGraphCheck.RawData.Valid and SensitivityGraphCheck.exists_215_success, https://prove2.me/definitions/e1bc7543-e6c9-4767-be0c-1d4085276993 and https://prove2.me/theorems/6d9893d7-40bb-47ea-acc7-3d8575b5e246. Exact source clauses: coherence, each tolerance-indexed defect bound, and the source-set bound of RawData.Valid. The numerical recurrence and dominance pruning are unchanged from SensitivityVariableFrontier. The subset argument uses Mathlib Finset.exists_subset_card_eq and Finset.powersetCard. This contribution supplies no successful 2.15 witness; the local-check existence theorem is the explicitly open residual problem.

import Definitions.Def_SensitivityGraphLocal

theorem SensitivityGraphLocal.exists_215_success :
    ∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphLocal.succeeds D (n + 1) k = true := by sorry
