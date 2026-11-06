-- Prove2me | Theorems.Thm_RecursionWithPieces_Forms_togetherAllOccur
-- name    : RecursionWithPieces.Forms.togetherAllOccur
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:02.138827+00:00
-- url     : https://prove2.me/theorems/fdbeb617-7763-4cc6-8db1-f4c5c70eb75c
-- title:
--   Forms: together All Occur
-- statement:
--   Through `RecursionWithPieces.tiedAllCal`: ONE machine and ONE constant C satisfy the bound of
--   Theorem 1, the bound of Theorem D (b) and the bound of Corollary 11, for formulas over x₀ … xₙ₋₁.
--   Names none of the objects of proof/variables/RecursionWithPieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Forms.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Forms.lean#L36-L36

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

theorem RecursionWithPieces.Forms.togetherAllOccur : TogetherAllOccur := by sorry
