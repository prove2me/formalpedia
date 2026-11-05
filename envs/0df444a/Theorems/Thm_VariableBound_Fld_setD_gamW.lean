-- Prove2me | Theorems.Thm_VariableBound_Fld_setD_gamW
-- name    : VariableBound.Fld.setD_gamW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:55:59.201637+00:00
-- url     : https://prove2.me/theorems/a28c9cf2-36ad-431f-9033-37d489b20101
-- title:
--   Fld: set D gam W
-- statement:
--   Let X^s + g be irreducible, s ≥ 1 the length of g, and m ≤ 2^s. For a quadruple u of words of s
--   bits, the list `gamW m a g u` lists the set Γ_u of Lemma 13 (Family of checks), for v = 2^a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L111-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L111-L132

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

theorem VariableBound.Fld.setD_gamW (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    setD m (gamW m a g u) = AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u) := by sorry
