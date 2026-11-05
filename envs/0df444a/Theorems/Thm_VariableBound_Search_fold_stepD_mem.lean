-- Prove2me | Theorems.Thm_VariableBound_Search_fold_stepD_mem
-- name    : VariableBound.Search.fold_stepD_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:37.096206+00:00
-- url     : https://prove2.me/theorems/d319a282-e249-41c0-8ff6-4fcacc3bab27
-- title:
--   Search: fold step D mem
-- statement:
--   The state of `argminD` is empty or a pair (l, key l) for a member l of the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L63-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L63-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
omit [Enc α]

theorem VariableBound.Search.fold_stepD_mem (key : List ℕ → ℤ) (S : List (List ℕ)) : ∀ (r : List (List ℕ)) (c : Option (List ℕ × ℤ)), (∀ l ∈ r, l ∈ S) →
    (c = none ∨ ∃ l ∈ S, c = some (l, key l)) → (r.foldl (stepD key) c = none ∨ ∃ l ∈ S, r.foldl (stepD key) c = some (l, key l)) := by sorry
