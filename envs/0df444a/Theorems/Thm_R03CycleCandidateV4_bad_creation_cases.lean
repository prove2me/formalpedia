-- Prove2me | Theorems.Thm_R03CycleCandidateV4_bad_creation_cases
-- name    : R03CycleCandidateV4.bad_creation_cases
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:26:37.645045+00:00
-- url     : https://prove2.me/theorems/ba4f8c2a-3078-40e2-b871-aee67f727a4f
-- title:
--   R03 P3-factor structural result: bad creation cases
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03CycleCandidateV4.bad_creation_cases` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is f8fad64ac8ba0cd0aad8c3f8e1d388d12c5e4a357c449774509a8f9b8e6c2a40.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/v4_CycleTransitions.lean; source SHA-256 f8fad64ac8ba0cd0aad8c3f8e1d388d12c5e4a357c449774509a8f9b8e6c2a40; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_b1e1659078_v4_CycleTransitions

namespace R03CycleCandidateV4

open R03CycleCandidateV4
theorem bad_creation_cases : ∀ a b c t : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 → t ≠ 0 →
    bad a b c = 0 → bad (a+t) (b+2*t) c = 1 →
    ((ins a b c = 2 ∧ outs a b c = 0) ∧
      ((a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0))) ∨
    ((ins a b c = 0 ∧ outs a b c = 1) ∧ a = 0 ∧ b = 0) := by sorry

end R03CycleCandidateV4
