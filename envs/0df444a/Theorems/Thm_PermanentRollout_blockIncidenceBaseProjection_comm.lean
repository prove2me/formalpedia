-- Prove2me | Theorems.Thm_PermanentRollout_blockIncidenceBaseProjection_comm
-- name    : PermanentRollout.blockIncidenceBaseProjection_comm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/c692bc90-43aa-4c12-a4cf-e8bccd4eae02
-- title:
--   PermanentRollout.blockIncidenceBaseProjection_comm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.blockIncidenceBaseProjection_comm
    (b t s d : ℕ) (block : Fin b) :
    (blockIncidenceBaseProjection b t s d).comp
        (MvPolynomial.rename
          (fun z : IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2)) =>
            (block, z))) =
      (blockIncidenceSingleBlockInclusion b t s d block).comp
        (partitionIncidenceGlobalBaseProjection t s d) := by sorry
