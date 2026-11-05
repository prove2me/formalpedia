-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Group_le_B_of_b549728d8dae
-- name    : P2M_GeneralPieces_Group_le_B_of_b549728d8dae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:13.662195+00:00
-- url     : https://prove2.me/theorems/9d8fa8f9-2592-4599-82c7-e829a6a5a6de
-- title:
--   P2 M General Pieces Group le B of b549728d8dae: P2 M General Pieces Group le B of b549728d8dae
-- statement:
--   P·⌊2g/K⌋ + g²B ≤ B' = ⌈2gP/K⌉ + g²B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L226-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/Lemma.lean#L226-L234

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
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col

theorem P2M_GeneralPieces_Group_le_B_of_b549728d8dae (K g P B : ℕ) (hK : 0 < K) : P * (2 * g / K) + B * g ^ 2 ≤ AppRunningTime.B'of K g P B := by sorry

alias «GeneralPieces».«Group».«le_B'of» := P2M_GeneralPieces_Group_le_B_of_b549728d8dae
