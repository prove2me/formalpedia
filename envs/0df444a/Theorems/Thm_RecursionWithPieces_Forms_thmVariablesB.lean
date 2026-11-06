-- Prove2me | Theorems.Thm_RecursionWithPieces_Forms_thmVariablesB
-- name    : RecursionWithPieces.Forms.thmVariablesB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:07.532908+00:00
-- url     : https://prove2.me/theorems/74a1d07e-17a2-4374-afbd-205666ef859f
-- title:
--   Forms: thm Variables B
-- statement:
--   Through `RecursionWithPieces.tiedAllCal`: Theorem D (b), the conclusion. Names none of the
--   objects of proof/variables/RecursionWithPieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Forms.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Forms.lean#L40-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_RecursionWithPieces_Forms
set_option autoImplicit false
section
section
open RecursionWithPieces RecursionWithPieces.Forms
open MainTheoremForms VariableBound.Paper RecursionWithPieces

theorem RecursionWithPieces.Forms.thmVariablesB : ThmVariablesB := by sorry
