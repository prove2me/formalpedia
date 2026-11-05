-- Prove2me | Theorems.Thm_VariableBound_Net_Val_netVal
-- name    : VariableBound.Net.Val.netVal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:45:12.289656+00:00
-- url     : https://prove2.me/theorems/5d45a356-e2ea-49c0-a83b-20702e41b38c
-- title:
--   Val: net Val
-- statement:
--   The value of the network of the profile y is the sum, over the assignments σ and the sets P of
--   objects whose clauses σ violates, of the term of P if P belongs to y. Needs that the labels
--   determine the strings (StLab), g > 0 and well-formed data (WfD).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L639-L657
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L639-L657

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.netVal (hL : StLab) (hg : 0 < g) (hw : WfD k n D) :
    (netDN g (ctx g n D y fl)).value =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) D).powerset, by classical exact if Match g n D y P then wt D fl P else 0 := by sorry
