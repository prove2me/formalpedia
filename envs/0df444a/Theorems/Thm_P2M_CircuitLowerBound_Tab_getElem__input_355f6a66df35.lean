-- Prove2me | Theorems.Thm_P2M_CircuitLowerBound_Tab_getElem__input_355f6a66df35
-- name    : P2M_CircuitLowerBound_Tab_getElem__input_355f6a66df35
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:42:40.971171+00:00
-- url     : https://prove2.me/theorems/5d84f813-757b-4cd5-aabe-bb987067098c
-- title:
--   P2 M Circuit Lower Bound Tab get Elem  input 355f6a66df35: P2 M Circuit Lower Bound Tab get Elem  input 355f6a66df35
-- statement:
--   The P2 M Circuit Lower Bound Tab get Elem  input 355f6a66df35 construction uses the P2 M Circuit Lower Bound Tab get Elem  input 355f6a66df35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Complete.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Complete.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Complete
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool) [Finite (Case N)]
variable {N}
omit [Finite (Case N)]

theorem P2M_CircuitLowerBound_Tab_getElem__input_355f6a66df35 (P : ℕ) (y : List Bool) {q : ℕ} (hq : q < P) :
    ((unary P ++ y).map N.inputAlphabet.invFun)[q]? = some (N.inputAlphabet.symm true) := by sorry

alias «CircuitLowerBound».«Tab».«getElem?_input» := P2M_CircuitLowerBound_Tab_getElem__input_355f6a66df35
