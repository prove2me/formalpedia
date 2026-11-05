-- Prove2me | Theorems.Thm_PaddedDescent_exists_tm_padded
-- name    : PaddedDescent.exists_tm_padded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:17.277176+00:00
-- url     : https://prove2.me/theorems/f5b5dba1-868c-4a81-8a9a-8539fd68d108
-- title:
--   Padded Descent: exists tm padded
-- statement:
--   Let `e` (from bit strings to numbers) and `A` (from a bit string and a list of units to a bit)
--   be polynomial-time. There are a
--   Turing machine `N` with finite alphabets and a number `q` such that on every bit string `x` the
--   machine halts with the output
--   A (x, the list of 2^(e x) units) within q · (|x| + 2^(e x) + 1)^q steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L116-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L116-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

theorem PaddedDescent.exists_tm_padded (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ x : List Bool,
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some ([A (x, pad (e x))].map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ e x + 1) ^ q)) := by sorry
