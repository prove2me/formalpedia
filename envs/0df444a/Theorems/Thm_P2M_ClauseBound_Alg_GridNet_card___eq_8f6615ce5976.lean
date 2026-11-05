-- Prove2me | Theorems.Thm_P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976
-- name    : P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:10.365588+00:00
-- url     : https://prove2.me/theorems/e2f34ec1-ce45-4ed1-91ca-64b6c64065ce
-- title:
--   P2 M Clause Bound Alg Grid Net card   eq 8f6615ce5976: P2 M Clause Bound Alg Grid Net card   eq 8f6615ce5976
-- statement:
--   The number of rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L212-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L212-L214

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976 (p d : ℕ) : #(Ω (Fin p) (Fin d)) = nRectG p d := by sorry

alias «ClauseBound».«Alg».«GridNet».«card_Ω_eq» := P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976
