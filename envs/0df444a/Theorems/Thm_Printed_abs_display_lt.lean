-- Prove2me | Theorems.Thm_Printed_abs_display_lt
-- name    : Printed.abs_display_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:58.201377+00:00
-- url     : https://prove2.me/theorems/9c789aa4-9695-491b-8a1e-9e0fafc9a52f
-- title:
--   Printed: abs display lt
-- statement:
--   **«So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B»**, strictly: at most 2^{P⌊2g/K⌋} terms, each at
--   most (2^B − 1)^{g²} < 2^{g²B}, since g, B ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L266-L282
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L266-L282

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Printed.abs_display_lt (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (hg : 0 < g) (x L : ℕ) (hG1 : ∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g)
    (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    |display Np c N hK0 x γ Θ| < 2 ^ bitsOut K g P B := by sorry
