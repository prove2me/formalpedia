-- Prove2me | Theorems.Thm_P2M_Eight_delta__le_fd4e6e087c27
-- name    : P2M_Eight_delta__le_fd4e6e087c27
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:13:29.604856+00:00
-- url     : https://prove2.me/theorems/46ed5136-6a7b-4fd9-b000-67245c3fca81
-- title:
--   P2 M Eight delta  le fd4e6e087c27: P2 M Eight delta  le fd4e6e087c27
-- statement:
--   «Let … δ' = δ/(3M) ≤ 1/3», for δ ≤ 1 and M ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L54-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L54-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_CountKSat_Value
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_Eight_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper

theorem P2M_Eight_delta__le_fd4e6e087c27 {δ M : ℝ} (hδ1 : δ ≤ 1) (hM : 1 ≤ M) : δ / (3 * M) ≤ 1 / 3 := by sorry

alias «Eight».«delta'_le» := P2M_Eight_delta__le_fd4e6e087c27
