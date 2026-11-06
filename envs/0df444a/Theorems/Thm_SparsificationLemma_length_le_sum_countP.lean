-- Prove2me | Theorems.Thm_SparsificationLemma_length_le_sum_countP
-- name    : SparsificationLemma.length_le_sum_countP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:34.906674+00:00
-- url     : https://prove2.me/theorems/e40a4d36-71b5-4033-b107-686d1b3f8428
-- title:
--   Sparsification Lemma: length le sum count P
-- statement:
--   If every member of a list has one of the properties p 0, …, p (n−1), the length of the list is
--   at most the sum over v < n of the number of members with the property p v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Len.lean#L28-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Len.lean#L28-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_SparsificationLemma_Len
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)

theorem SparsificationLemma.length_le_sum_countP {α : Type} (n : ℕ) (p : ℕ → α → Bool) (L : List α) (h : ∀ a ∈ L, ∃ v < n, p v a = true) :
    L.length ≤ ∑ v ∈ range n, L.countP (p v) := by sorry
