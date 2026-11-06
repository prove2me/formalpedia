-- Prove2me | Theorems.Thm_SplitCount_leafPlain_polyT
-- name    : SplitCount.leafPlain_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:40.9682+00:00
-- url     : https://prove2.me/theorems/36253263-9b5c-44b8-8ef9-11c9b617360d
-- title:
--   Split Count: leaf Plain poly T
-- statement:
--   What is counted at a node is computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L41-L43

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

theorem SplitCount.leafPlain_polyT : PolyT leafPlain := by sorry
