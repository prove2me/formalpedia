-- Prove2me | Theorems.Thm_ThmCount_holds_pad4
-- name    : ThmCount.holds_pad4
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:52.83077+00:00
-- url     : https://prove2.me/theorems/ef75eb4c-8bf6-489d-bcd4-c3c9ad8ba902
-- title:
--   Thm Count: holds pad4
-- statement:
--   An assignment satisfies `pad4 φ` exactly if, read on the old variables, it satisfies φ, and it
--   gives the four new variables the value 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L85-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L85-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode

theorem ThmCount.holds_pad4 {n : ℕ} (φ : Sat3.CNF n) (b : Fin (n + 4) → Bool) :
    (∀ D ∈ Wrap.pad4 φ, ∃ l ∈ D, b l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, b (Fin.castAdd 4 l.1) = l.2) ∧ ∀ j : Fin 4, b (Fin.natAdd n j) = true := by sorry
