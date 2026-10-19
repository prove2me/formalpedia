-- Prove2me | Theorems.Thm_PermanentRollout_sourceCircuit_ofList_ofFn_eq_span_range
-- name    : PermanentRollout.sourceCircuit_ofList_ofFn_eq_span_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/236585ca-6e20-4279-813f-5b5e4a59072e
-- title:
--   PermanentRollout.sourceCircuit_ofList_ofFn_eq_span_range
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.sourceCircuit_ofList_ofFn_eq_span_range
    {R : Type*} [CommSemiring R] {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by sorry
