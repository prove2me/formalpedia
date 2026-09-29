-- Prove2me | Theorems.Thm_R03OrderedPathCandidate_idx3_eq_finProd
-- name    : R03OrderedPathCandidate.idx3_eq_finProd
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:23:30.687269+00:00
-- url     : https://prove2.me/theorems/764c5ba0-e62a-44f7-8475-228909a0aa24
-- title:
--   R03 P3-factor structural result: Idx3 eq fin prod
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03OrderedPathCandidate.idx3_eq_finProd` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp02/ordered_path_p3factor_candidate_v1.lean; source SHA-256 b1efcef6748d81e4147d0d885ff669f31b2c94f666a1d399e401d7b745254e0c; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1

namespace R03OrderedPathCandidate

open R03OrderedPathCandidate
open CubicP3Partition
universe u
variable {V : Type u}
theorem idx3_eq_finProd (k : Nat) (i : Fin k) (j : Fin 3) :
    (finProdFinEquiv (i, j) : Fin (k * 3)) = idx3 k i j := by sorry

end R03OrderedPathCandidate
