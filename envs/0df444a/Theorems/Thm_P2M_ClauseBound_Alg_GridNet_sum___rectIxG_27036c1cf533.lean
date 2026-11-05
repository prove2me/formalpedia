-- Prove2me | Theorems.Thm_P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533
-- name    : P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:57.577206+00:00
-- url     : https://prove2.me/theorems/98d76f53-55c7-4a76-9a08-be43dfb43bed
-- title:
--   P2 M Clause Bound Alg Grid Net sum   rect Ix G 27036c1cf533: P2 M Clause Bound Alg Grid Net sum   rect Ix G 27036c1cf533
-- statement:
--   The same for the rectangles sorted by parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L269-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L269-L275

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

theorem P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533 (p d : ℕ) (tr : Bool) (f : ℕ → ℕ) :
    ∑ ω ∈ Ω (Fin (nParts p d tr)) (Fin (nMemb p d tr)), f (rectIxG d tr (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2)) =
      ∑ q ∈ range (nRectG p d), f q := by sorry

alias «ClauseBound».«Alg».«GridNet».«sum_Ω_rectIxG» := P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533
