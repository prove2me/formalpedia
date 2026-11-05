-- Prove2me | Theorems.Thm_VariableBound_Fld_decQ_surj
-- name    : VariableBound.Fld.decQ_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:18.974249+00:00
-- url     : https://prove2.me/theorems/e0565fb4-62ce-49d4-88a1-d5d3cb92919d
-- title:
--   Fld: dec Q surj
-- statement:
--   Every quadruple of residues is written by a quadruple of words of s bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L98-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L98-L105

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
attribute [local instance] fintypeFW

theorem VariableBound.Fld.decQ_surj (g : List Bool) (w : FW g × FW g × FW g × FW g) :
    ∃ u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length, decQ g u = w := by sorry
