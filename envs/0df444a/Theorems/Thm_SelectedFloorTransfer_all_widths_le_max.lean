-- Prove2me | Theorems.Thm_SelectedFloorTransfer_all_widths_le_max
-- name    : SelectedFloorTransfer.all_widths_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/57d42f7e-2497-4e2d-a9de-bc3da9814528
-- title:
--   SelectedFloorTransfer: All widths le max
-- statement:
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L15-L16). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L15-L16 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate

theorem SelectedFloorTransfer.all_widths_le_max : rows.all (fun r => decide (r.width ≤ maxChild)) = true := by sorry
