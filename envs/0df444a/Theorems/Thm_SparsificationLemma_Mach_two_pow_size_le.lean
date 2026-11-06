-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_two_pow_size_le
-- name    : SparsificationLemma.Mach.two_pow_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:56.310317+00:00
-- url     : https://prove2.me/theorems/271ffe93-f35f-44bd-b1aa-46c78b4a4bcb
-- title:
--   Mach: two pow size le
-- statement:
--   2 to the number of binary digits of N ≥ 1 is at most 2N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Main.lean#L38-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Main.lean#L38-L45

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
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

theorem SparsificationLemma.Mach.two_pow_size_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ Nat.size N ≤ 2 * N := by sorry
