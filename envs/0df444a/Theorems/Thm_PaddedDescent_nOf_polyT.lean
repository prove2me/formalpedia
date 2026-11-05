-- Prove2me | Theorems.Thm_PaddedDescent_nOf_polyT
-- name    : PaddedDescent.nOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:51.671372+00:00
-- url     : https://prove2.me/theorems/ea9162b4-ef92-4517-9542-837a7d0f2d74
-- title:
--   Padded Descent: n Of poly T
-- statement:
--   The Padded Descent construction uses the n Of poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/BrutePad.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/BrutePad.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Batteries.Data.Nat.Lemmas
import Definitions.Def_PaddedDescent_BrutePad
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing

theorem PaddedDescent.nOf_polyT : PolyT nOf := by sorry
