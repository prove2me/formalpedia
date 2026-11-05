-- Prove2me | Theorems.Thm_SelectedFloorTransfer_all_width_cost_bound
-- name    : SelectedFloorTransfer.all_width_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/5436c9b7-8210-4e85-b5e1-8fd6fc3c31f0
-- title:
--   SelectedFloorTransfer: All width cost bound
-- statement:
--   An unconditional analytic characteristic and a constructive finite-base constant reduce every integer-width power bound to this exact cost contract. No monotonicity assumption on f or ceiling-envelope cost is present.
--
--   Specialization of floor-depth and recurrence bounds to the selected profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L58-L73). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/SelectedFloorTransfer.lean#L58-L73 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate

theorem SelectedFloorTransfer.all_width_cost_bound (f : ℕ → ℝ) (C : ℝ)
    (physical_recurrence : ∀ e, m ≤ e →
      f e ≤ C + (rows.map (fun r => (r.multiplicity : ℝ) / W *
        f (r.width * (e / m)))).sum) :
    ∀ e, 0 < e → f e ≤ costConstant f C * (e : ℝ) ^ (1 - (saving : ℝ)) := by sorry
