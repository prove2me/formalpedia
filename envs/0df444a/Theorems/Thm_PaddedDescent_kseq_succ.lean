-- Prove2me | Theorems.Thm_PaddedDescent_kseq_succ
-- name    : PaddedDescent.kseq_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:08.64152+00:00
-- url     : https://prove2.me/theorems/28189366-a7a9-45ea-8870-2ee0942196ff
-- title:
--   Padded Descent: kseq succ
-- statement:
--   k_{j+1} = 2·(k_j + 47 + j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Params.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Params.lean#L35-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
import Definitions.Def_PaddedDescent_Params
set_option autoImplicit false
section
section
open PaddedDescent
attribute [local semireducible] kseq

theorem PaddedDescent.kseq_succ (j : ℕ) : kseq (j + 1) = 2 * (kseq j + 47 + j) := by sorry
