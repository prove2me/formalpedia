-- Prove2me | Theorems.Thm_P2M_Eight_SecCrossing_Cert_prodL_polyT__d947e175e279
-- name    : P2M_Eight_SecCrossing_Cert_prodL_polyT__d947e175e279
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:14:56.984437+00:00
-- url     : https://prove2.me/theorems/9e0c1501-aeb1-4118-a706-a10d8fda2d81
-- title:
--   P2 M Eight Sec Crossing Cert prod L poly T  d947e175e279: P2 M Eight Sec Crossing Cert prod L poly T  d947e175e279
-- statement:
--   A product over s < n is polynomial-time, for n in unary; the factors need to be polynomial-time
--   only at indices cut off at n (min(s, n)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L47-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L47-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]

theorem P2M_Eight_SecCrossing_Cert_prodL_polyT__d947e175e279 {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => prodL (n x) (f x) := by sorry

alias «Eight».«SecCrossing_Cert».«prodL_polyT'» := P2M_Eight_SecCrossing_Cert_prodL_polyT__d947e175e279
