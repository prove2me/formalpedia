-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_two_pow_precE_le
-- name    : SparsificationLemma.Mach.two_pow_precE_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:20.750165+00:00
-- url     : https://prove2.me/theorems/aaa2d03b-4f39-45fa-a4f0-d58163d72c63
-- title:
--   Mach: two pow prec E le
-- statement:
--   C·2^s ≤ 4·(Ck/ε)² for s = `precE C k ε`, if C ≥ 1, k ≥ 1 and ε ∈ (0,1].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L65-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L65-L93

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

theorem SparsificationLemma.Mach.two_pow_precE_le {C k : ℕ} {ε : ℚ} (hC : 1 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (C : ℝ) * (2 : ℝ) ^ precE C k ε ≤ 4 * ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ 2 := by sorry
