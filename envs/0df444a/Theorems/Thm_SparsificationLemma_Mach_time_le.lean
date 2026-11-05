-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_time_le
-- name    : SparsificationLemma.Mach.time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:11:20.289194+00:00
-- url     : https://prove2.me/theorems/3593d906-5a58-48b1-a606-9dc17328c46c
-- title:
--   Mach: time le
-- statement:
--   The time of the padding machine is within the bound of the statement, with C = q·4097^q + 4q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Main.lean#L48-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Main.lean#L48-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Cert
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Main
import Theorems.Thm_ClauseBound_Alg_End_time_le

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

theorem SparsificationLemma.Mach.time_le (q a k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    q * (N + 2 ^ (a + k + 3 * Nat.size N + 9) + 1) ^ q ≤ (q * 4097 ^ q + 4 * q) * (N + 2 ^ k) ^ (q * 4097 ^ q + 4 * q) * 2 ^ ((q * 4097 ^ q + 4 * q) * a) := by sorry
