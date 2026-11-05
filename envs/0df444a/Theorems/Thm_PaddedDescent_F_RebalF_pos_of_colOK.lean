-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_pos_of_colOK
-- name    : PaddedDescent.F.RebalF.pos_of_colOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:08.663567+00:00
-- url     : https://prove2.me/theorems/6dca2c0d-1464-4392-9755-ef20a6a2d660
-- title:
--   Rebal F: pos of col OK
-- statement:
--   From `ColOK K g` and K ≥ 1: g is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalG.lean#L89-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalG.lean#L89-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_PaddedDescent_F_RebalG
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.Col Finset

theorem PaddedDescent.F.RebalF.pos_of_colOK {K g : ℕ} (hK : 1 ≤ K) (h : ColOK K g) : 0 < g := by sorry
