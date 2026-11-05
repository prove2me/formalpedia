-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_patterns_polyT
-- name    : PaddedDescent.F.CertGrid.patterns_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:58:15.1372+00:00
-- url     : https://prove2.me/theorems/dc54f90b-1b68-4cb2-8416-92a9aabfb5de
-- title:
--   Cert Grid: patterns poly T
-- statement:
--   The list of the patterns, cut off by the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L100-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L100-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertGrid.patterns_polyT {pad gu : α → U} {I : α → PInst} (hp : PolyT pad) (hg : PolyT gu) (hI : PolyT I) :
    PolyT fun x => rng (pad x) (((I x).1.length + 1) ^ nRect (gu x).length) := by sorry
