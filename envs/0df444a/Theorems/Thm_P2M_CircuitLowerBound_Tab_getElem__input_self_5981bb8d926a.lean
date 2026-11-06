-- Prove2me | Theorems.Thm_P2M_CircuitLowerBound_Tab_getElem__input_self_5981bb8d926a
-- name    : P2M_CircuitLowerBound_Tab_getElem__input_self_5981bb8d926a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:42:47.337273+00:00
-- url     : https://prove2.me/theorems/ccb0b1e4-8461-40a9-b080-913e1f23d425
-- title:
--   P2 M Circuit Lower Bound Tab get Elem  input self 5981bb8d926a: P2 M Circuit Lower Bound Tab get Elem  input self 5981bb8d926a
-- statement:
--   The P2 M Circuit Lower Bound Tab get Elem  input self 5981bb8d926a construction uses the P2 M Circuit Lower Bound Tab get Elem  input self 5981bb8d926a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Complete.lean#L43-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Complete.lean#L43-L45

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

theorem P2M_CircuitLowerBound_Tab_getElem__input_self_5981bb8d926a (P : ℕ) (y : List Bool) :
    ((unary P ++ y).map N.inputAlphabet.invFun)[P]? = some (N.inputAlphabet.symm false) := by sorry

alias «CircuitLowerBound».«Tab».«getElem?_input_self» := P2M_CircuitLowerBound_Tab_getElem__input_self_5981bb8d926a
