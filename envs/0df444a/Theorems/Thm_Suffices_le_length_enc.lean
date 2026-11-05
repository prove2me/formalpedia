-- Prove2me | Theorems.Thm_Suffices_le_length_enc
-- name    : Suffices.le_length_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:29:31.294053+00:00
-- url     : https://prove2.me/theorems/1d577860-cffa-423f-a6e6-5b2831c2974e
-- title:
--   Suffices: le length enc
-- statement:
--   The number of variables and the number of clauses are at most N, the length of the code plus 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L46-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L46-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)

theorem Suffices.le_length_enc {n : ℕ} (φ : Sat3.CNF n) : n ≤ (Sat3.enc φ).length + 1 ∧ φ.length ≤ (Sat3.enc φ).length + 1 := by sorry
