-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_mul_div_le_eps
-- name    : SparsificationLemma.Mach.mul_div_le_eps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:41.039812+00:00
-- url     : https://prove2.me/theorems/d9ec0461-5cc1-461b-9d92-102f9dd3196e
-- title:
--   Mach: mul div le eps
-- statement:
--   c·⌊n/2^s⌋ ≤ εn, if c ≤ C, C/ε ≤ 2^s and ε > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L115-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L115-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Geo_S
import Definitions.Def_SparsificationLemma_Mach_Len
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_Full
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing

theorem SparsificationLemma.Mach.mul_div_le_eps {c C n s : ℕ} {ε : ℝ} (hc : c ≤ C) (h0 : 0 < ε) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    ((c * (n / 2 ^ s) : ℕ) : ℝ) ≤ ε * (n : ℝ) := by sorry
