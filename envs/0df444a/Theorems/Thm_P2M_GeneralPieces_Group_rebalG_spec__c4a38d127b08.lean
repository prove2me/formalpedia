-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08
-- name    : P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:02.069758+00:00
-- url     : https://prove2.me/theorems/79c7e1a4-1cde-456f-accd-f51eae3ee731
-- title:
--   P2 M General Pieces Group rebal G spec  c4a38d127b08: P2 M General Pieces Group rebal G spec  c4a38d127b08
-- statement:
--   "Find the first such grouping among all K^g, define the (K, L)-clique with the tables W̃_γ,
--   whose value is that of the network": if some grouping passes the test for the label length β and the
--   pad
--   is long enough, `rebalG` returns the clique on K nodes with labels of β bits, written out, with the
--   value of the network and entries of absolute value at most 2^{P·⌊2g/K⌋ + g²B}. This is
--   `PaddedDescent.F.RebalF.rebalG_spec` with the paper's bound on the entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L153-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L153-L209

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col

theorem P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08 {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ)
    (hK : 2 ≤ K) (hg0 : 0 < g) (hβ1 : 1 ≤ β) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B)
    (hex : ∃ x < K ^ g, goodG K g F.toP β (c, x) = true)
    (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧ WF K β (P * (2 * g / K) + B * g ^ 2) J := by sorry

alias «GeneralPieces».«Group».«rebalG_spec'» := P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08
