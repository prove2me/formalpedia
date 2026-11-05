-- Prove2me | Theorems.Thm_P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764
-- name    : P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:26.128546+00:00
-- url     : https://prove2.me/theorems/5b85a303-a69f-49b9-8640-ead6c5e24196
-- title:
--   P2 M Circuit Lower Bound Tab get Elem  pref 6e5abd1d4764: P2 M Circuit Lower Bound Tab get Elem  pref 6e5abd1d4764
-- statement:
--   In a list of cells in which a blank is followed by blanks only, the symbols up to the first
--   blank have the cells as their entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L143-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L143-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing

theorem P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764 {α : Type} : ∀ L : List (Option α), (∀ i, L[i]? = some none → ∀ x, L[i + 1]? = some x → x = none) →
    ∀ q, q < L.length → (pref L)[q]? = (L[q]?).getD none
  := by sorry

alias «CircuitLowerBound».«Tab».«getElem?_pref» := P2M_CircuitLowerBound_Tab_getElem__pref_6e5abd1d4764
