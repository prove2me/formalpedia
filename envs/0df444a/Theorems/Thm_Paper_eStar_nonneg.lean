-- Prove2me | Theorems.Thm_Paper_eStar_nonneg
-- name    : Paper.eStar_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:55:50.12468+00:00
-- url     : https://prove2.me/theorems/a3629bbc-f248-439e-84c5-6abd325a63bf
-- title:
--   Paper: e Star nonneg
-- statement:
--   0 ≤ e*.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L136-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L136-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset

theorem Paper.eStar_nonneg : 0 ≤ eStar := by sorry
