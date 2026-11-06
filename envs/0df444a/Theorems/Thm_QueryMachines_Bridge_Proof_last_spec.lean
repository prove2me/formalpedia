-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_last_spec
-- name    : QueryMachines.Bridge.Proof.last_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:04.564339+00:00
-- url     : https://prove2.me/theorems/e69ac0a1-d9f8-4079-9c61-a4d9761b1fe0
-- title:
--   Proof: last spec
-- statement:
--   After the first m numbers: nothing, if no K_ℓ with ℓ < m is within the bound; else the entry of
--   the largest such ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L60-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L60-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.last_spec {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) : ∀ m : ℕ, m ≤ b.length + 1 →
    (((List.range m).filterMap (cand kf b)).getLast? = none ∧ ∀ l < m, b.length < K l) ∨
    ∃ l < m, ((List.range m).filterMap (cand kf b)).getLast? = some (unary l, (unary l, unary (K l))) ∧ K l ≤ b.length ∧ ∀ l', l < l' → l' < m → b.length < K l' := by sorry
