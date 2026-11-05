-- Prove2me | Theorems.Thm_SelectedFloorTransfer_costConstant_nonneg
-- name    : SelectedFloorTransfer.costConstant_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/e09f4677-e806-422f-9f66-76ef1ad87a5f
-- title:
--   SelectedFloorTransfer: Cost Constant nonneg
-- statement:
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L51-L53). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L51-L53 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate

theorem SelectedFloorTransfer.costConstant_nonneg (f : ℕ → ℝ) (C : ℝ) : 0 ≤ costConstant f C := by sorry
