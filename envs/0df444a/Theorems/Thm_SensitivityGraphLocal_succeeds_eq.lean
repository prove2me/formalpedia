-- Prove2me | Theorems.Thm_SensitivityGraphLocal_succeeds_eq
-- name    : SensitivityGraphLocal.succeeds_eq
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-06T18:57:29.171609+00:00
-- url     : https://prove2.me/theorems/5bc256f8-4873-4b21-a2bb-789ea8d8989d
-- title:
--   Exact-sized graph checks preserve the sensitivity search result
-- statement:
--   For every raw graph-and-labeling input $D$, every state count $n$, and every depth $k$, the checker that tests only forbidden-size subsets returns the same Boolean result as the original checker:
--
--   $$\operatorname{localSearch}(D,n,k)=\operatorname{checkedSearch}(D,n,k).$$
--
--   All original graph conditions are retained. Only the ordinary, defect, and source labeling checks are restricted to subsets of exactly their forbidden cardinalities. The finite profile search is unchanged. This identifies an equivalent validation procedure, including rejection of invalid inputs. It does not assert that a successful input exists.
-- source:
--   Original hereditary-subset reduction of SensitivityGraphCheck.RawData.Valid and SensitivityGraphCheck.exists_215_success, https://prove2.me/definitions/e1bc7543-e6c9-4767-be0c-1d4085276993 and https://prove2.me/theorems/6d9893d7-40bb-47ea-acc7-3d8575b5e246. Exact source clauses: coherence, each tolerance-indexed defect bound, and the source-set bound of RawData.Valid. The numerical recurrence and dominance pruning are unchanged from SensitivityVariableFrontier. The subset argument uses Mathlib Finset.exists_subset_card_eq and Finset.powersetCard. This contribution supplies no successful 2.15 witness; the local-check existence theorem is the explicitly open residual problem.

import Definitions.Def_SensitivityGraphLocal

theorem SensitivityGraphLocal.succeeds_eq
    (D : SensitivityGraphCheck.RawData) (n k : ℕ) :
    SensitivityGraphLocal.succeeds D n k = SensitivityGraphCheck.succeeds D n k := by sorry
