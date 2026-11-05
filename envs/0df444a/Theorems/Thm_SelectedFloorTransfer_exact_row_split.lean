-- Prove2me | Theorems.Thm_SelectedFloorTransfer_exact_row_split
-- name    : SelectedFloorTransfer.exact_row_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/28207fce-bd37-49f8-a7f9-be938d23a24e
-- title:
--   SelectedFloorTransfer: Exact row split
-- statement:
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L40-L41). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L40-L41 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate

theorem SelectedFloorTransfer.exact_row_split (e R : ℕ) (he : m ≤ e) (stock : W ^ depth e ∣ R) :
    W * (R / W) = R := by sorry
