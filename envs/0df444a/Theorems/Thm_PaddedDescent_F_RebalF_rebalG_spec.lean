-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_rebalG_spec
-- name    : PaddedDescent.F.RebalF.rebalG_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:06.072205+00:00
-- url     : https://prove2.me/theorems/060b046c-29da-4144-8517-6bb76de8f6b2
-- title:
--   Rebal F: rebal G spec
-- statement:
--   The rebalancing with a given label length β: if some colouring below K^g is good for β and the
--   pad is long enough, `rebalG` returns an explicit instance on K nodes
--   with labels of β bits and the value of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalG.lean#L27-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalG.lean#L27-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_PaddedDescent_F_RebalG
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.Col Finset

theorem PaddedDescent.F.RebalF.rebalG_spec {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ)
    (hK : 2 ≤ K) (hg0 : 0 < g) (hβ1 : 1 ≤ β) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B)
    (hex : ∃ x < K ^ g, goodG K g F.toP β (c, x) = true)
    (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧
      WF K β (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) J := by sorry
