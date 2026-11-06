-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_layersOf_unary
-- name    : PaddedDescent.F.CertTop.layersOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:41:16.685121+00:00
-- url     : https://prove2.me/theorems/9e3ec66f-54a2-478f-9238-9fe23e785129
-- title:
--   Cert Top: layers Of unary
-- statement:
--   The number of layers is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L123-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L123-L125

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

theorem PaddedDescent.F.CertTop.layersOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => layersOf (sOf (n x)) := by sorry
