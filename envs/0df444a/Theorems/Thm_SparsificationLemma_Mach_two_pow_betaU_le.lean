-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_two_pow_betaU_le
-- name    : SparsificationLemma.Mach.two_pow_betaU_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:31.778774+00:00
-- url     : https://prove2.me/theorems/57193205-a59d-40c7-969a-089d6041bbcd
-- title:
--   Mach: two pow beta U le
-- statement:
--   Part (c): 2^(2k(4s+17)) ≤ (Ck/ε)^(16k) for s = `precE C k ε`, if C ≥ 81, k ≥ 1 and ε ∈ (0,1].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L96-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean#L96-L112

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

theorem SparsificationLemma.Mach.two_pow_betaU_le {C k : ℕ} {ε : ℚ} (hC : 81 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (2 : ℝ) ^ betaU k (precE C k ε) ≤ ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ (16 * k) := by sorry
