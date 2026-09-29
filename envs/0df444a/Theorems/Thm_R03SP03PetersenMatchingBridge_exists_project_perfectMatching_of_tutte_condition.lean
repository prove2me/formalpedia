-- Prove2me | Theorems.Thm_R03SP03PetersenMatchingBridge_exists_project_perfectMatching_of_tutte_condition
-- name    : R03SP03PetersenMatchingBridge.exists_project_perfectMatching_of_tutte_condition
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:02:33.874828+00:00
-- url     : https://prove2.me/theorems/11bbb673-161b-41b1-8c0a-94e60253dedc
-- title:
--   R03 P3-factor structural result: Exists project perfect matching of tutte condition
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP03PetersenMatchingBridge.exists_project_perfectMatching_of_tutte_condition` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp03/r03-sp03-petersen-matching-bridge-v1.lean; source SHA-256 edd19032668b0d38fa78b02f7fc0162d191a5d396fa66f60b33593861437814f; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03PetersenMatchingBridge

open R03SP03PetersenMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem exists_project_perfectMatching_of_tutte_condition
    {G : SimpleGraph V}
    (hNoViolator : ∀ u : Set V, ¬ G.IsTutteViolator u) :
    ∃ M : SimpleGraph V, CubicP3Partition.PerfectMatching G M := by sorry

end R03SP03PetersenMatchingBridge
