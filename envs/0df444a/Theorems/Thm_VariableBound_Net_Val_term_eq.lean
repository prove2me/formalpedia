-- Prove2me | Theorems.Thm_VariableBound_Net_Val_term_eq
-- name    : VariableBound.Net.Val.term_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:45:18.572597+00:00
-- url     : https://prove2.me/theorems/ec981487-85bc-4711-a00a-08a26219e7a8
-- title:
--   Val: term eq
-- statement:
--   One term of the value: the product of the weights at a good family of settings that has the
--   numbers of the profile, and 0 at every other family. Needs that the labels determine the strings
--   (StLab).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L602-L633
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Val.lean#L602-L633

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
import Theorems.Thm_Groundwork_SatNet_term_eq

set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}

theorem VariableBound.Net.Val.term_eq (hL : StLab) (z : Fin g → List Bool) :
    (∏ a, (netDN g (ctx g n D y fl)).W a (z a)) *
        ∏ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
      by classical exact if Gd g n D z then
        (if ∀ a : Fin g, prof g n D y a (z a) = true then ∏ a : Fin g, wz g n D fl a (z a) else 0) else 0 := by sorry
