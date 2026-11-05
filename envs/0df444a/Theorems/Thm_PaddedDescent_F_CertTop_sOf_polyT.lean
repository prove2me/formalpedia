-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_sOf_polyT
-- name    : PaddedDescent.F.CertTop.sOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:39:14.690203+00:00
-- url     : https://prove2.me/theorems/5c168d80-62e8-4029-b125-0f52e250d412
-- title:
--   Cert Top: s Of poly T
-- statement:
--   The precision sOf n is polynomial-time in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L90-L92

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

theorem PaddedDescent.F.CertTop.sOf_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => sOf (n x) := by sorry
