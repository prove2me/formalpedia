-- Prove2me | Theorems.Thm_P2M_Groundwork_tuples_congr__2a63300181ad
-- name    : P2M_Groundwork_tuples_congr__2a63300181ad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:01.53037+00:00
-- url     : https://prove2.me/theorems/3531b928-e1d7-49ff-be14-3ee7c008509e
-- title:
--   P2 M Groundwork tuples congr  2a63300181ad: P2 M Groundwork tuples congr  2a63300181ad
-- statement:
--   Tuples depend on the sets only where the predicate holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L60-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L60-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset

theorem P2M_Groundwork_tuples_congr__2a63300181ad {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {T T' : ι → Finset X}
    (d : X) (h : ∀ i, P i → T i = T' i) : tuples P T d = tuples P T' d := by sorry

alias «Groundwork».«tuples_congr'» := P2M_Groundwork_tuples_congr__2a63300181ad
