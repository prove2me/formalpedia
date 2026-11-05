-- Prove2me | Theorems.Thm_VariableBound_mul_pow_mono
-- name    : VariableBound.mul_pow_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:03.904492+00:00
-- url     : https://prove2.me/theorems/e0846045-5483-40b3-b578-757c46d6f5ff
-- title:
--   Variable Bound: mul pow mono
-- statement:
--   q·y^q grows with q, for y ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/Tied.lean#L26-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/Tied.lean#L26-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_VariableBound_Printed_Tied
set_option autoImplicit false
section
section
open VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide

theorem VariableBound.mul_pow_mono {q C y : ℕ} (h : q ≤ C) (hy : 1 ≤ y) : q * y ^ q ≤ C * y ^ C := by sorry
