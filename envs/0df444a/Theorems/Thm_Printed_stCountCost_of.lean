-- Prove2me | Theorems.Thm_Printed_stCountCost_of
-- name    : Printed.stCountCost_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:02.407828+00:00
-- url     : https://prove2.me/theorems/a3b319e1-572d-46f9-8fa6-b3128491d932
-- title:
--   Printed: st Count Cost of
-- statement:
--   **Section 6, «Cost», for Count**, from «(K_ℓ, e_ℓ) is achievable» by Clique(ℓ), Lemma 1 for the
--   algorithm of its proof, its polynomial-time steps, and Lemma 1 for networks given by procedures.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L210-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L210-L218

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.stCountCost_of (hC : StClique) (hG : StGroupingTied) (hGp : StGroupingPoly) (hOn : StOnProcedures) : StCountCost := by sorry
