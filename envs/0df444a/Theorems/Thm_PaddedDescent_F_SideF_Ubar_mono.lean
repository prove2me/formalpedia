-- Prove2me | Theorems.Thm_PaddedDescent_F_SideF_Ubar_mono
-- name    : PaddedDescent.F.SideF.Ubar_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:39.190014+00:00
-- url     : https://prove2.me/theorems/16dc17d5-5e2f-44b0-8a12-2d1a8a647125
-- title:
--   Side F: Ubar mono
-- statement:
--   `Ubar g` is monotone in the label length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L67-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.SideF.Ubar_mono {g a b : ℕ} (h : a ≤ b) : Ubar g a ≤ Ubar g b := by sorry
