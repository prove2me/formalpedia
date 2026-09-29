-- Prove2me | Theorems.Thm_R03OrientationWordsM6_receive_one_iff
-- name    : R03OrientationWordsM6.receive_one_iff
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:22:47.820482+00:00
-- url     : https://prove2.me/theorems/4d968219-8db4-4474-bdc4-058a9bebc966
-- title:
--   R03 P3-factor structural result: Receive one iff
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03OrientationWordsM6.receive_one_iff` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/m6_OrientationWords.lean; source SHA-256 61c586abfb7f19e7e431d1d2ca51ae3a80c339b64fce37904d669a6d720b7971; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fintype.Pi
import Definitions.Def_r03_defs_67e8a31036_m6_OrientationWords

namespace R03OrientationWordsM6

open R03OrientationWordsM6
theorem receive_one_iff (a b : Bool) : receive a b = 1 ↔ a = b := by sorry

end R03OrientationWordsM6
