-- Prove2me | Theorems.Thm_UniformInK_End_boundNK_mono
-- name    : UniformInK.End.boundNK_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:45:36.108241+00:00
-- url     : https://prove2.me/theorems/71d409d9-8006-4016-8297-bbdfcf702697
-- title:
--   End: bound NK mono
-- statement:
--   The bound in n with k² in the exponent grows with the constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L26-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L26-L30

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

theorem UniformInK.End.boundNK_mono {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k n : ℕ) (hr : 0 ≤ r n) : SatM.boundNK r D k n ≤ SatM.boundNK r D' k n := by sorry
