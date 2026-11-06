-- Prove2me | Theorems.Thm_VariableBound_Net_Main_certAdm
-- name    : VariableBound.Net.Main.certAdm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:08.845211+00:00
-- url     : https://prove2.me/theorems/5465c997-aa4e-4a5a-8e42-d9550cef89cf
-- title:
--   Main: cert Adm
-- statement:
--   The test «admissible» is polynomial-time, for g given in unary and the other arguments
--   polynomial-time (`StCertAdm`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Main.lean#L125-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Main.lean#L125-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_VariableBound_Net_CertRank
import Definitions.Def_VariableBound_Net_Val
import Definitions.Def_VariableBound_Net_Prof
import Definitions.Def_VariableBound_Net_Tuples
import Definitions.Def_VariableBound_Net_Total
import Definitions.Def_VariableBound_Net_SizeU
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Definitions.Def_VariableBound_Net_Fit
import Definitions.Def_VariableBound_Net_Ev
import Definitions.Def_VariableBound_Net_CertNet
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_VariableBound_Net_Main
import Theorems.Thm_PaddedDescent_F_certAdm

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Main

theorem VariableBound.Net.Main.certAdm : StCertAdm := by sorry
