-- Prove2me | Theorems.Thm_P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f
-- name    : P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:15.6563+00:00
-- url     : https://prove2.me/theorems/f2655bc7-97eb-4b4d-9395-48846b940a30
-- title:
--   P2 M Clause Bound Alg Grid Net sum   ix G ea3994ec108f: P2 M Clause Bound Alg Grid Net sum   ix G ea3994ec108f
-- statement:
--   A sum over the rectangles is the sum over their numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L264-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L264-L266

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

theorem P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f (p d : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin p) (Fin d), f (ixG p d ω) = ∑ q ∈ range (nRectG p d), f q := by sorry

alias «ClauseBound».«Alg».«GridNet».«sum_Ω_ixG» := P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f
