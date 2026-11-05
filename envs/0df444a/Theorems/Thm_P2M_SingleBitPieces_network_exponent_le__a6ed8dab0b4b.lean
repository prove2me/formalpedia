-- Prove2me | Theorems.Thm_P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b
-- name    : P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:29:29.623045+00:00
-- url     : https://prove2.me/theorems/5fceb084-114f-49fd-b356-a3f10ae6df68
-- title:
--   P2 M Single Bit Pieces network exponent le  a6ed8dab0b4b: P2 M Single Bit Pieces network exponent le  a6ed8dab0b4b
-- statement:
--   «… ≤ ¾δ'm + δ'g.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecProof_Cost.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecProof_Cost.lean#L55-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper

theorem P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) : δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 3 / 4 * δ' * m + δ' * g := by sorry

alias «SingleBitPieces».«network_exponent_le'» := P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b
