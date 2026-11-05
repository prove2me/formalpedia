-- Prove2me | Theorems.Thm_VariableBound_Fld_decQ_inj
-- name    : VariableBound.Fld.decQ_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:45.247899+00:00
-- url     : https://prove2.me/theorems/18820cc9-0776-449d-b6c2-f752db2c23cb
-- title:
--   Fld: dec Q inj
-- statement:
--   Distinct quadruples of words of s bits stand for distinct quadruples of residues.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L88-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L88-L95

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

theorem VariableBound.Fld.decQ_inj (g : List Bool) {u u' : List Bool × List Bool × List Bool × List Bool}
    (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length)
    (hu' : u' ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) (h : decQ g u = decQ g u') : u = u' := by sorry
