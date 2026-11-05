-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_sum_range_eq
-- name    : PaddedDescent.F.Mark.Cert.sum_range_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:30:52.013324+00:00
-- url     : https://prove2.me/theorems/5d6a9b8a-ec95-4fc6-a495-ea1fe71da25a
-- title:
--   Cert: sum range eq
-- statement:
--   In a double sum over a' < a < g the inner range can be cut out of the outer one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L230-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L230-L234

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]

theorem PaddedDescent.F.Mark.Cert.sum_range_eq (g : ℕ) (F : ℕ → ℕ → ℕ) : ((List.range g).map fun a => ((List.range a).map fun a' => F a' a).sum).sum =
    ((List.range g).map fun a => (((List.range g).take a).map fun a' => F a' a).sum).sum := by sorry
