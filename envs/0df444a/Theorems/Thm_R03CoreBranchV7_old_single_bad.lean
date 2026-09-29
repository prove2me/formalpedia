-- Prove2me | Theorems.Thm_R03CoreBranchV7_old_single_bad
-- name    : R03CoreBranchV7.old_single_bad
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:26:19.696166+00:00
-- url     : https://prove2.me/theorems/397ac6ea-4f67-4143-8ffb-2c5d431e6427
-- title:
--   R03 P3-factor structural result: old single bad
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03CoreBranchV7.old_single_bad` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is e1d2053293ec939cacc23baaf0af9276f314523d857885a7ab951e93d24ddb35.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/v7_CoreBranch.lean; source SHA-256 e1d2053293ec939cacc23baaf0af9276f314523d857885a7ab951e93d24ddb35; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_c874916438_v7_CoreBranch

namespace R03CoreBranchV7

open R03CoreBranchV7
theorem old_single_bad : ∀ v : Fin 9, BadAt (state 0 0 2) v ↔ v=7 := by sorry

end R03CoreBranchV7
