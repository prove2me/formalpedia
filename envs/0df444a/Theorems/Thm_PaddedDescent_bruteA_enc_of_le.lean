-- Prove2me | Theorems.Thm_PaddedDescent_bruteA_enc_of_le
-- name    : PaddedDescent.bruteA_enc_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:15:28.26132+00:00
-- url     : https://prove2.me/theorems/2fa2d379-a26e-498f-9c3b-1600510376cb
-- title:
--   Padded Descent: brute A enc of le
-- statement:
--   With a pad of length at least 2^n, exhaustive search finds a satisfying assignment exactly if
--   there is one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/BrutePad.lean#L61-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/BrutePad.lean#L61-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Batteries.Data.Nat.Lemmas
import Definitions.Def_PaddedDescent_BrutePad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing

theorem PaddedDescent.bruteA_enc_of_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) {w : List Unit} (hw : 2 ^ n ≤ w.length) :
    bruteA (enc φ, w) = true ↔ Satisfiable φ := by sorry
