-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_len_list_le
-- name    : PaddedDescent.F.Top.len_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:59:02.805384+00:00
-- url     : https://prove2.me/theorems/984c203f-f5e5-487b-8b38-436e7cdce337
-- title:
--   Top: len list le
-- statement:
--   A bound on the length of the word of a list of at most k members, each with a word of length at
--   most s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L67-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L67-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.len_list_le {α : Type} [Enc α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, len x ≤ s) :
    len l ≤ k * (s + 2) + 2 := by sorry
