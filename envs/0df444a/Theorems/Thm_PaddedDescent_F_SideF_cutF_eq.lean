-- Prove2me | Theorems.Thm_PaddedDescent_F_SideF_cutF_eq
-- name    : PaddedDescent.F.SideF.cutF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:00.144023+00:00
-- url     : https://prove2.me/theorems/be754419-2382-4bb3-b4e8-f66735feef59
-- title:
--   Side F: cut F eq
-- statement:
--   `cutF` is `cutW`, if the pad has at least 2^|x| units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L28-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L28-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.SideF.cutF_eq {pad : U} (tr top : Bool) (i : ℕ) {x : List Bool} (y w : List Bool) (h : 2 ^ x.length ≤ pad.length) :
    cutF pad tr top i x y w = cutW tr top i x y w := by sorry
