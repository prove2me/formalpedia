-- Prove2me | Theorems.Thm_VariableBound_Rename_clausesOf_bodyOf
-- name    : VariableBound.Rename.clausesOf_bodyOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:53:45.653847+00:00
-- url     : https://prove2.me/theorems/0dc3a6d2-24db-442f-a086-4d16fc456fdf
-- title:
--   Rename: clauses Of body Of
-- statement:
--   Reading the bits of the clauses with the width ⌊log₂(2N)⌋ + 1 gives the formula back, for k ≥ 1
--   and φ with at most k literals in every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L59-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L59-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)

theorem VariableBound.Rename.clausesOf_bodyOf {k N : ℕ} (hk : 1 ≤ k) {φ : CNF N} (hφ : ∀ C ∈ φ, C.length ≤ k) : clausesOf k (Nat.log2 (2 * N) + 1) (bodyOf k φ) = toN φ := by sorry
