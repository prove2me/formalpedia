-- Prove2me | Theorems.Thm_VariableBound_Fld_all_take_iff
-- name    : VariableBound.Fld.all_take_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:01.048605+00:00
-- url     : https://prove2.me/theorems/118d0d72-faed-49ce-b6f3-7a7a8e82dfb5
-- title:
--   Fld: all take iff
-- statement:
--   The first k bits of a word w of n bits are 0, as a test on the list and as a statement on the
--   places i < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L30-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L30-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial

theorem VariableBound.Fld.all_take_iff {n : ℕ} {w : List Bool} (hw : w.length = n) (k : ℕ) :
    ((w.take k).all fun b => !b) = true ↔ ∀ i : Fin n, i.val < k → w.getD i.val false = false := by sorry
