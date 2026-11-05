-- Prove2me | Theorems.Thm_VariableBound_Fld_length_gamW
-- name    : VariableBound.Fld.length_gamW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:04.931557+00:00
-- url     : https://prove2.me/theorems/3cb3ed93-fe6f-4fa2-81d6-209955db4696
-- title:
--   Fld: length gam W
-- statement:
--   Let X^s + g be irreducible, s ≥ 1 the length of g, and m ≤ 2^s. For a quadruple u of words of s
--   bits, the list `gamW m a g u` has |Γ_u| members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L136-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L136-L139

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

theorem VariableBound.Fld.length_gamW (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    (gamW m a g u).length = #(AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u)) := by sorry
