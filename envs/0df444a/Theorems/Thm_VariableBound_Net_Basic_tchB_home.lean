-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_tchB_home
-- name    : VariableBound.Net.Basic.tchB_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:09.919195+00:00
-- url     : https://prove2.me/theorems/cffc8cd3-ca2a-47ea-b90c-4a331220402a
-- title:
--   Basic: tch B home
-- statement:
--   An incidence (E, j) touches h(j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L152-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L152-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.tchB_home {o : ℕ} (h1 : (obAt D o).1 = 1) : tchB g n D (home g (obAt D o).2.2) o = true := by sorry
