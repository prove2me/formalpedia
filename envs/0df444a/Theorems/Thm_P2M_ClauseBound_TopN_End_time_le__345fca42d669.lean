-- Prove2me | Theorems.Thm_P2M_ClauseBound_TopN_End_time_le__345fca42d669
-- name    : P2M_ClauseBound_TopN_End_time_le__345fca42d669
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:21:39.41921+00:00
-- url     : https://prove2.me/theorems/bfbf541a-f4ce-4bfe-9d69-dfc2eb4a0511
-- title:
--   P2 M Clause Bound Top N End time le  345fca42d669: P2 M Clause Bound Top N End time le  345fca42d669
-- statement:
--   If L + 1 ≤ a·2^(H·X) and E ≤ G·X then q·(L + 2^E + 1)^q ≤ C·2^(C·X) with C = q·(a+1)^q + q·(H +
--   G).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/End.lean#L43-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/End.lean#L43-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_TopN_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End

theorem P2M_ClauseBound_TopN_End_time_le__345fca42d669 (q L E a H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hL : ((L + 1 : ℕ) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * X)) (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤
      ((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * X) := by sorry

alias «ClauseBound».«TopN».«End».«time_le'» := P2M_ClauseBound_TopN_End_time_le__345fca42d669
