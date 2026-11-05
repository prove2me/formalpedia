-- Prove2me | Theorems.Thm_P2M_PaddedDescent_exists_tm__adb177e912aa
-- name    : P2M_PaddedDescent_exists_tm__adb177e912aa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:15.254851+00:00
-- url     : https://prove2.me/theorems/ab0ec698-3d85-423b-9686-d45e2b83f8af
-- title:
--   P2 M Padded Descent exists tm  adb177e912aa: P2 M Padded Descent exists tm  adb177e912aa
-- statement:
--   A stepped computation `M` on bit strings with polynomial-time init, step and out runs on one of
--   Mathlib's multi-stack
--   machines `N` with finite alphabets. There is one number `q` such that, whenever `M` ends on `x` with
--   the bit `b` within `T`
--   steps and with all states of size at most `S`, the machine `N` started on `x` halts with output `b`
--   within
--   q · (T + 1) · (|x| + S + 1)^q steps. `N` and `q` depend on `M` only: not on `x`, `T`, `S`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Host.lean#L32-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Host.lean#L32-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_PaddedDescent_Host
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.TM Groundwork.Host Turing

theorem P2M_PaddedDescent_exists_tm__adb177e912aa (M : Stepped (List Bool) Bool) [IsPolyT M] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (b : Bool), M.Runs x T S b →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some ([b].map N.outputAlphabet.invFun))
          (q * (T + 1) * (x.length + S + 1) ^ q)) := by sorry

alias «PaddedDescent».«exists_tm'» := P2M_PaddedDescent_exists_tm__adb177e912aa
