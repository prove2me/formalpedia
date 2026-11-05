-- Prove2me | Theorems.Thm_Sat3_inRateTM_of_mulForm
-- name    : Sat3.inRateTM_of_mulForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:16.112613+00:00
-- url     : https://prove2.me/theorems/4680ae16-8b6d-4ac1-888d-44a91ae199c1
-- title:
--   Sat3: in Rate TM of mul Form
-- statement:
--   A machine with finite alphabets that decides 3-SAT within t n ≤ A·2^(e n) steps, for any
--   exponents with e n · 2^(sOf n) ≤ C₁·(n + 2^(sOf n)), witnesses the rate statement with c = 3/19.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L148-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean#L148-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal

theorem Sat3.inRateTM_of_mulForm (M : TM2ComputableAux Bool Bool) (hfin : ∀ k, Finite (M.tm.Γ k)) (A C₁ : ℕ) (t e : ℕ → ℕ)
    (h : DecidesTM M t) (ht : ∀ n, t n ≤ A * 2 ^ e n)
    (he : ∀ n, e n * 2 ^ PaddedDescent.sOf n ≤ C₁ * (n + 2 ^ PaddedDescent.sOf n)) : InRateTM (3 / 19) := by sorry
