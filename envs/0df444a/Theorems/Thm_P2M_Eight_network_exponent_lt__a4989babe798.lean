-- Prove2me | Theorems.Thm_P2M_Eight_network_exponent_lt__a4989babe798
-- name    : P2M_Eight_network_exponent_lt__a4989babe798
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:32:40.411908+00:00
-- url     : https://prove2.me/theorems/c5e13771-17f5-4429-b827-6707e8d7e7d9
-- title:
--   P2 M Eight network exponent lt  a4989babe798: P2 M Eight network exponent lt  a4989babe798
-- statement:
--   «… ≤ ¾δ'm + δ'g.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L397-L402
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L397-L402

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

theorem P2M_Eight_network_exponent_lt__a4989babe798 {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 3 / 4 * δ' * m + δ' * g := by sorry

alias «Eight».«network_exponent_lt'» := P2M_Eight_network_exponent_lt__a4989babe798
