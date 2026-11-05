-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_linkB_polyT
-- name    : PaddedDescent.F.Mark.Cert.linkB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:21:31.586672+00:00
-- url     : https://prove2.me/theorems/395937d9-4f25-412a-8e69-29957a09de92
-- title:
--   Cert: link B poly T
-- statement:
--   The test «a and b are neighbours in the chain of clause e»; g is in unary because the test runs
--   through all nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L57-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L57-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]

theorem PaddedDescent.F.Mark.Cert.linkB_polyT {g n e a b : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls) (he : PolyT e)
    (ha : PolyT a) (hb : PolyT b) : PolyT fun x => linkB (g x) (n x) (Ls x) (e x) (a x) (b x) := by sorry
