-- Prove2me | Theorems.Thm_UniformInK_End_boundBothK_of_ge
-- name    : UniformInK.End.boundBothK_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:22.176312+00:00
-- url     : https://prove2.me/theorems/599751f7-0395-48bd-93bc-b45cec348a5e
-- title:
--   End: bound Both K of ge
-- statement:
--   If the exponent in m is the smaller one, the bound with the minimum is the bound in m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L39-L42

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

theorem UniformInK.End.boundBothK_of_ge {rn rm : ℕ → ℝ} {C k n m : ℕ} (h : (k : ℝ) * m * rm m ≤ (k : ℝ) ^ 2 * n * rn n) : SatM.boundBothK rn rm C k n m = SatM.bound rm C k m := by sorry
