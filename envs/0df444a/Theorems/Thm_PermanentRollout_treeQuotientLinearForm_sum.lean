-- Prove2me | Theorems.Thm_PermanentRollout_treeQuotientLinearForm_sum
-- name    : PermanentRollout.treeQuotientLinearForm_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/36f6c324-8915-4e02-82f6-40b50c7ebcf6
-- title:
--   PermanentRollout.treeQuotientLinearForm_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.treeQuotientLinearForm_sum {r : ℕ} {ι : Type*}
    (indices : Finset ι) (vectors : ι → Fin r → ℂ) :
    treeQuotientLinearForm (fun row => ∑ i ∈ indices, vectors i row) =
      ∑ i ∈ indices, treeQuotientLinearForm (vectors i) := by sorry
