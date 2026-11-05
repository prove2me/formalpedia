-- Prove2me | Theorems.Thm_P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2
-- name    : P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:04.804199+00:00
-- url     : https://prove2.me/theorems/838f1a77-b1a7-4352-9a9b-31d72fd3a36e
-- title:
--   P2 M Eight Via Grouping psi Lt eq   8a678fd56db2: P2 M Eight Via Grouping psi Lt eq   8a678fd56db2
-- statement:
--   Both directions at once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L103-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L103-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level

theorem P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2 {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a < b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    psiLt g tr lam y a b z z' = (netOfι g tr lam y Rm).Ψ a b z z' := by sorry

alias «Eight».«ViaGrouping».«psiLt_eq_Ψ» := P2M_Eight_ViaGrouping_psiLt_eq___8a678fd56db2
