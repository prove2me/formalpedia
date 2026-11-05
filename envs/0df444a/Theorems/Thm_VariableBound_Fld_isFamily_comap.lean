-- Prove2me | Theorems.Thm_VariableBound_Fld_isFamily_comap
-- name    : VariableBound.Fld.isFamily_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:39:02.735476+00:00
-- url     : https://prove2.me/theorems/f9d36809-0e52-4924-87ef-eb5422894682
-- title:
--   Fld: is Family comap
-- statement:
--   (a), (b), (c) of Lemma 13 (Family of checks) pass along an injective map φ of index sets with Ω =
--   φ(Ω').
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L85-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L85-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset

theorem VariableBound.Fld.isFamily_comap {E ι ι' : Type} [Fintype E] [DecidableEq E] {v : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (h : AppVariables.IsFamily v Ω Γ)
    (φ : ι' ↪ ι) (Ω' : Finset ι') (hΩ : Ω = Ω'.map φ) : AppVariables.IsFamily v Ω' fun i => Γ (φ i) := by sorry
