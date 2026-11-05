-- Prove2me | Theorems.Thm_PaddedDescent_F_SideF_capM_mono
-- name    : PaddedDescent.F.SideF.capM_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:01.409104+00:00
-- url     : https://prove2.me/theorems/5a03cd82-a1cb-44f5-89bd-1995ccec64fc
-- title:
--   Side F: cap M mono
-- statement:
--   `capM g` is monotone in the label length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L74-L76

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

theorem PaddedDescent.F.SideF.capM_mono {g a b : ℕ} (h : a ≤ b) : capM g a ≤ capM g b := by sorry
