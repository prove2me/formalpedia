-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_ceilMul_poly
-- name    : QueryMachines.Bridge.Proof.ceilMul_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:46.588376+00:00
-- url     : https://prove2.me/theorems/f0447f9c-36dd-4923-803f-0d142c2bdbd7
-- title:
--   Proof: ceil Mul poly
-- statement:
--   Rounding up is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/SolverPoly.lean#L25-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/SolverPoly.lean#L25-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_CountedToPadded_SolverPoly
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

theorem QueryMachines.Bridge.Proof.ceilMul_poly {α : Type} [Enc α] {a b n : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hn : PolyT n) : PolyT fun x => ceilMul (a x) (b x) (n x) := by sorry
