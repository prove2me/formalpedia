-- Prove2me | Theorems.Thm_SelectedFloorTransfer_child_depth_drop
-- name    : SelectedFloorTransfer.child_depth_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/508642d1-6a56-4db7-97bc-a080e29be618
-- title:
--   SelectedFloorTransfer: Child depth drop
-- statement:
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L32-L34). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L32-L34 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorDepth_child_depth_drop

set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate

theorem SelectedFloorTransfer.child_depth_drop (r : Row) (hr : r ∈ rows) (e : ℕ) (he : m ≤ e) :
    depth (r.width * (e / m)) + 1 ≤ depth e := by sorry
