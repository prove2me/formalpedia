-- Prove2me | Theorems.Thm_P2M_ClauseBound_Alg_CertEnum_query0_polyT__f2a8702ae01f
-- name    : P2M_ClauseBound_Alg_CertEnum_query0_polyT__f2a8702ae01f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:30.80913+00:00
-- url     : https://prove2.me/theorems/db4ad11f-1f39-4ac4-be2b-bfb35f5dec15
-- title:
--   P2 M Clause Bound Alg Cert Enum query0 poly T  f2a8702ae01f: P2 M Clause Bound Alg Cert Enum query0 poly T  f2a8702ae01f
-- statement:
--   The query at the node v, with the number K of nodes in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L182-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L182-L184

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}

theorem P2M_ClauseBound_Alg_CertEnum_query0_polyT__f2a8702ae01f {K ℓ v : α → ℕ} {d w : α → List Bool} (hK : Unary K) (h1 : PolyT ℓ) (h2 : PolyT d) (h3 : PolyT w) (h4 : PolyT v) :
    PolyT fun x => query0 (K x) (ℓ x) (d x) (w x) (v x) := by sorry

alias «ClauseBound».«Alg».«CertEnum».«query0_polyT'» := P2M_ClauseBound_Alg_CertEnum_query0_polyT__f2a8702ae01f
