-- Prove2me | Theorems.Thm_SplitCount_stCert
-- name    : SplitCount.stCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:30.319905+00:00
-- url     : https://prove2.me/theorems/e922b17d-acc8-4a8c-86d0-baa0e3d07cb6
-- title:
--   Split Count: st Cert
-- statement:
--   The steps of `timesFreeAfter Cnt` are polynomial time if those of Cnt are; the steps of
--   `engineBy step D` are polynomial time if `step` is polynomial-time and the steps of D are polynomial
--   time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L48-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L48-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_SplitCount_Cert
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat Eight.Width Occ

theorem SplitCount.stCert : StCert := by sorry
