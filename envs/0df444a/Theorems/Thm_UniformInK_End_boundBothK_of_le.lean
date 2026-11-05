-- Prove2me | Theorems.Thm_UniformInK_End_boundBothK_of_le
-- name    : UniformInK.End.boundBothK_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:45:34.228386+00:00
-- url     : https://prove2.me/theorems/a602fbfa-1444-4638-a564-e6240fec567b
-- title:
--   End: bound Both K of le
-- statement:
--   If the exponent in n is the smaller one, the bound with the minimum is the bound in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L33-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L33-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_UniformInK_Top_End
set_option autoImplicit false
section
section
open UniformInK UniformInK.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End

theorem UniformInK.End.boundBothK_of_le {rn rm : ℕ → ℝ} {C k n m : ℕ} (h : (k : ℝ) ^ 2 * n * rn n ≤ (k : ℝ) * m * rm m) : SatM.boundBothK rn rm C k n m = SatM.boundNK rn C k n := by sorry
