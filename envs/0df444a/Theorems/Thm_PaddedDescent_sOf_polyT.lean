-- Prove2me | Theorems.Thm_PaddedDescent_sOf_polyT
-- name    : PaddedDescent.sOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:48.713839+00:00
-- url     : https://prove2.me/theorems/62df9952-2cbf-4065-9c89-25b36d868435
-- title:
--   Padded Descent: s Of poly T
-- statement:
--   `sOf` of a polynomial-time function is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L34-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing

theorem PaddedDescent.sOf_polyT {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT fun x => sOf (f x) := by sorry
