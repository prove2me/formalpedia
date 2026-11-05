-- Prove2me | Theorems.Thm_SingleBitPieces_network_exponent_le
-- name    : SingleBitPieces.network_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:29:30.97771+00:00
-- url     : https://prove2.me/theorems/b6ca5574-c088-4b49-8186-52498a91ffac
-- title:
--   Single Bit Pieces: network exponent le
-- statement:
--   **Section 6, «Cost».** «With e = δ'/12, K ≥ 72 and 1/K ≤ δ'/72, the exponent in Lemma 1 is eU +
--   e·gP/K + 2gP/K < ½δ'm + (1/144)δ'(m + g) + (1/6)δ'(m + g) = (97/144)δ'm + (25/144)δ'g.» Same as in
--   the paper, except that
--   the inequality is not strict, because U ≤ 6m here (the paper: U < 6m). K ≥ 72 follows from K ≥ 72/δ'
--   and δ' ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecProof_Cost.lean#L28-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecProof_Cost.lean#L28-L52

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

theorem SingleBitPieces.network_exponent_le {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 97 / 144 * δ' * m + 25 / 144 * δ' * g := by sorry
