-- Prove2me | Theorems.Thm_Value_display_eq
-- name    : Value.display_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:51.916382+00:00
-- url     : https://prove2.me/theorems/9c9723f6-0e75-4e7c-befc-7034eaa1e4a1
-- title:
--   Value: display eq
-- statement:
--   If all appended bits of Λ are 0, the table of the group γ at the strings of Λ on the edges at γ
--   is the sum inside the table, with the strings θ_{a,b} that are read from Λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L45-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L45-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}

theorem Value.display_eq (hSB : StSameBlock) (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) {Λ : Fin K × Fin K → List Bool} (hA : AppendedZero g Np c x Λ) (γ : Fin K) :
    display Np c N hK0 x γ (star Λ γ) = ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [], groupTerm N (Paper.grouping hK0 x) (readBlocks Np c hK0 x Λ) γ z := by sorry
