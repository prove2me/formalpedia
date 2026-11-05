-- Prove2me | Theorems.Thm_VariableBound_Rename_anyBit_binary
-- name    : VariableBound.Rename.anyBit_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:07.093209+00:00
-- url     : https://prove2.me/theorems/82a1e10f-2061-4d14-bf67-af9fd20a587e
-- title:
--   Rename: any Bit binary
-- statement:
--   On a number c < 2^(n+1) written in n + 1 bits, `anyBit` says whether c ≠ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/End.lean#L38-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/End.lean#L38-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_VariableBound_Paper_Rename_End
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.Rename.anyBit_binary {n c : ℕ} (h : c < 2 ^ (n + 1)) : anyBit (SatK.binary n c) = [decide (c ≠ 0)] := by sorry
