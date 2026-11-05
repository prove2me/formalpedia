-- Prove2me | Theorems.Thm_VariableBound_Fld_isFamily_list
-- name    : VariableBound.Fld.isFamily_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:58.419199+00:00
-- url     : https://prove2.me/theorems/06883dd0-92fb-42ee-ae2c-f8101fa748f7
-- title:
--   Fld: is Family list
-- statement:
--   Let the list L have no repetitions, let D be injective on its members with image Ω, and let G u
--   list the set Γ (D u) for every member u of L. If the sets Γ_w, w ∈ Ω, have (a), (b), (c) of
--   Lemma 13 (Family of checks) for v, then the list `L.map G` has |Ω| members, and they, indexed by
--   their places, have (a), (b), (c) for v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L98-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L98-L124

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

theorem VariableBound.Fld.isFamily_list {m v : ℕ} {ι U : Type} (Ω : Finset ι) (Γ : ι → Finset (Fin m)) (L : List U) (D : U → ι) (G : U → List ℕ)
    (hL : L.Nodup) (hD : ∀ u ∈ L, ∀ u' ∈ L, D u = D u' → u = u') (hΩ : ∀ w, w ∈ Ω ↔ ∃ u ∈ L, D u = w)
    (hG : ∀ u ∈ L, setD m (G u) = Γ (D u)) (h : AppVariables.IsFamily v Ω Γ) :
    #Ω = (L.map G).length ∧ AppVariables.IsFamily v (univ : Finset (Fin (L.map G).length)) fun i => setD m ((L.map G).get i) := by sorry
