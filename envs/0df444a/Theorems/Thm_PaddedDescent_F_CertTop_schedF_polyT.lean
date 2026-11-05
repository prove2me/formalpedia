-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_schedF_polyT
-- name    : PaddedDescent.F.CertTop.schedF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:44.471162+00:00
-- url     : https://prove2.me/theorems/4bc0446b-23f3-458b-b4ee-005ff20480e4
-- title:
--   Cert Top: sched F poly T
-- statement:
--   The schedule, jointly in the pad and the number t of levels (in unary). Its start does not
--   depend on the input, and the pad caps every round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L49-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L49-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertTop.schedF_polyT {pad : α → U} {t : α → ℕ} (hp : PolyT pad) (ht : Unary t) : PolyT fun x => schedF (pad x) (t x) := by sorry
