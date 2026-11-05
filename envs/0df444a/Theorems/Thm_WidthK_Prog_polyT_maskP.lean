-- Prove2me | Theorems.Thm_WidthK_Prog_polyT_maskP
-- name    : WidthK.Prog.polyT_maskP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:34:53.615399+00:00
-- url     : https://prove2.me/theorems/bca42fa4-d78b-46c5-8d54-398731f36c58
-- title:
--   Prog: poly T mask P
-- statement:
--   Picking the sublist of a clause given by a mask is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L29-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L29-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
set_option autoImplicit false
section
section
open WidthK WidthK.Prog
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem WidthK.Prog.polyT_maskP {m : α → List Bool} {C : α → PCl} (hm : PolyT m) (hC : PolyT C) :
    PolyT fun x => maskP (m x) (C x) := by sorry
