-- Prove2me | Theorems.Thm_VariableBound_stTimeD
-- name    : VariableBound.stTimeD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:45.172281+00:00
-- url     : https://prove2.me/theorems/5bdd1c79-9502-4f8e-be36-c336944e22d6
-- title:
--   Variable Bound: st Time D
-- statement:
--   Step 6: the number of steps of a padding machine with the exponent function of the algorithm for
--   n is within the bound in n with k² in the exponent; the constant does not depend on k. Hypotheses:
--   the bound for the
--   exponent of a plan (`StArithD`), the exponent is at most n (`StPlanLeD`), and the decoding of the
--   input (`StDecM`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Time.lean#L41-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Time.lean#L41-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_VariableBound_Top_Time
set_option autoImplicit false
section
section
open VariableBound
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End UniformInK

theorem VariableBound.stTimeD (hA : StArithD) (hP : StPlanLeD) (hD : StDecM) : StTimeD := by sorry
