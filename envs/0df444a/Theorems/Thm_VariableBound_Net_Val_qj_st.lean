-- Prove2me | Theorems.Thm_VariableBound_Net_Val_qj_st
-- name    : VariableBound.Net.Val.qj_st
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:44.679179+00:00
-- url     : https://prove2.me/theorems/9ccfb7cc-ea46-423a-8a73-782e8dc6932b
-- title:
--   Val: qj st
-- statement:
--   «h(j) sees |Π_j|»: at the home of check j, the number of marked incidences of check j in the
--   setting of (σ, P) is the number of members of P that are incidences of check j, for a set P of
--   places of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L294-L306
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L294-L306

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_VariableBound_Net_Val
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.qj_st (σ : ℕ → Bool) {P : Finset ℕ} (hP : P ⊆ Finset.range (objs D).length) (j : ℕ) :
    qj g n D (home g j) (st g n D σ P (home g j)) j = (chP D P j).card := by sorry
