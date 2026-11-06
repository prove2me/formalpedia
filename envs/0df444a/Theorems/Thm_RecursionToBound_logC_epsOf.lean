-- Prove2me | Theorems.Thm_RecursionToBound_logC_epsOf
-- name    : RecursionToBound.logC_epsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:13.811101+00:00
-- url     : https://prove2.me/theorems/848d8103-c1c7-4a1d-b5c0-5d9287919785
-- title:
--   Recursion To Bound: log C eps Of
-- statement:
--   ⌈log₂ x⌉ of the thresholds, without fractions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L96-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L96-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.logC_epsOf (k : ℕ) (r : ℕ × ℕ) : Cal.logC k (epsOf r) = logN k r := by sorry
