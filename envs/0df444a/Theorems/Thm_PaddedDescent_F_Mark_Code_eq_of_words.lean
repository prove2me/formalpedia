-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_eq_of_words
-- name    : PaddedDescent.F.Mark.Code.eq_of_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:36.154125+00:00
-- url     : https://prove2.me/theorems/d8c3c6e8-9384-4e60-91d9-666d3d2b58a9
-- title:
--   Code: eq of words
-- statement:
--   Words of β bits of numbers below 2^β, laid end to end, are read back one by one, whatever
--   follows them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L52-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L52-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.eq_of_words {β : ℕ} : ∀ {P P' : List ℕ} {r r' : List Bool}, P.length = P'.length → (∀ p ∈ P, p < 2 ^ β) → (∀ p ∈ P', p < 2 ^ β) →
    P.flatMap (toWord β) ++ r = P'.flatMap (toWord β) ++ r' → P = P' ∧ r = r'
  := by sorry
