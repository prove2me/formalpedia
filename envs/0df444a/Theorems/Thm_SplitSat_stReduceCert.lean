-- Prove2me | Theorems.Thm_SplitSat_stReduceCert
-- name    : SplitSat.stReduceCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:59.259625+00:00
-- url     : https://prove2.me/theorems/ba2a8c65-0743-4cff-a3f9-3e07f97b737f
-- title:
--   Split Sat: st Reduce Cert
-- statement:
--   The steps of the reduction are polynomial time if those of D are: the statement
--   `SplitSat.StReduceCert`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L47-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L47-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Cert
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight.Width

theorem SplitSat.stReduceCert : StReduceCert := by sorry
