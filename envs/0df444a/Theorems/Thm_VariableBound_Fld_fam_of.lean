-- Prove2me | Theorems.Thm_VariableBound_Fld_fam_of
-- name    : VariableBound.Fld.fam_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:17.443003+00:00
-- url     : https://prove2.me/theorems/b8b82d5e-49d8-4917-9401-204578fcca8b
-- title:
--   Fld: fam of
-- statement:
--   Lemma 13 (Family of checks) for the list made with any word g of s bits for which X^s + g is
--   irreducible: let 1 ≤ a, 2^a ≤ m and 16m ≤ 2^s < 32m, and let Lemma 13 hold over every field with 2^s
--   elements. Then the list is not empty, has fewer than (32m)⁴ members, every member is an increasing
--   list of numbers below m, and the members, indexed by their places, have (a), (b), (c) for v = 2^a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L147-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L147-L181

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

theorem VariableBound.Fld.fam_of (h14 : AppVariables.LemFamily) (m a : ℕ) (g : List Bool) (ha : 1 ≤ a) (hm : 2 ^ a ≤ m) (hs1 : 16 * m ≤ 2 ^ g.length) (hs2 : 2 ^ g.length < 32 * m)
    (hirr : Irreducible (modP g)) (Lst : List (List ℕ))
    (hLst : Lst = ((wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length).filter fun u =>
      decide (2 ^ a * (gamW m a g u).length ≤ 16 * m)).map (gamW m a g)) :
    Lst ≠ [] ∧ Lst.length < (32 * m) ^ 4 ∧ (∀ l ∈ Lst, l.Pairwise (· < ·) ∧ l.Nodup ∧ ∀ E ∈ l, E < m) ∧
    AppVariables.IsFamily (2 ^ a) (Finset.univ : Finset (Fin Lst.length)) fun i => setD m (Lst.get i) := by sorry
