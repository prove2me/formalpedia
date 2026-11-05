-- Prove2me | Theorems.Thm_VariableBound_Decide_polyT_bitOf
-- name    : VariableBound.Decide.polyT_bitOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:25.434574+00:00
-- url     : https://prove2.me/theorems/4ca99114-64ca-4842-a894-5f3096c79d03
-- title:
--   Decide: poly T bit Of
-- statement:
--   «Some bit is 1» is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Decide.lean#L75-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Decide.lean#L75-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_VariableBound_Paper_Decide
set_option autoImplicit false
section
section
open VariableBound VariableBound.Decide
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Both.End UniformInK.End

theorem VariableBound.Decide.polyT_bitOf : PolyT bitOf := by sorry
