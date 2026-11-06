-- Prove2me | Theorems.Thm_P2M_CircuitLowerBound_stENP__443f046b8760
-- name    : P2M_CircuitLowerBound_stENP__443f046b8760
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:39:28.77803+00:00
-- url     : https://prove2.me/theorems/c8c464c6-baa3-4bb5-8797-227e4846b733
-- title:
--   P2 M Circuit Lower Bound st ENP  443f046b8760: P2 M Circuit Lower Bound st ENP  443f046b8760
-- statement:
--   The language is in E^NP, second form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Closed.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Closed.lean#L40-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Main
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CircuitLowerBound_Tab_Complete
import Definitions.Def_CircuitLowerBound_Tab_Pack
import Definitions.Def_CircuitLowerBound_Tab_Table
import Definitions.Def_CircuitLowerBound_Tab_Glue
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Definitions.Def_CircuitLowerBound_Circ_Norm
import Definitions.Def_CircuitLowerBound_Circ_Form
import Definitions.Def_CircuitLowerBound_Alg_Time
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Definitions.Def_CircuitLowerBound_Closed
set_option autoImplicit false
section
section
open CircuitLowerBound

theorem P2M_CircuitLowerBound_stENP__443f046b8760 : StENP' := by sorry

alias «CircuitLowerBound».«stENP'» := P2M_CircuitLowerBound_stENP__443f046b8760
