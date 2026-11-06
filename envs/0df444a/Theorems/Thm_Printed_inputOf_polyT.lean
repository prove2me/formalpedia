-- Prove2me | Theorems.Thm_Printed_inputOf_polyT
-- name    : Printed.inputOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:42:48.445117+00:00
-- url     : https://prove2.me/theorems/4b55d363-69a5-42ec-ab69-cf95ad1a29ff
-- title:
--   Printed: input Of poly T
-- statement:
--   The input of Definition 2(iii) is written down in polynomial time from numbers given in unary.
--   The number g of nodes is a constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L30-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L30-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_HandOver
set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {Q A C : Type}

theorem Printed.inputOf_polyT [Enc C] (g : ℕ) {P B : C → ℕ} {len : C → ℕ → ℕ} {cap : C → ℕ → ℕ → ℕ} (hP : Unary P) (hB : Unary B)
    (hl : Unary fun p : C × ℕ => len p.1 p.2) (hc : Unary fun p : C × ℕ × ℕ => cap p.1 p.2.1 p.2.2) :
    PolyT fun c => inputOf g (P c) (B c) (len c) (cap c) := by sorry
