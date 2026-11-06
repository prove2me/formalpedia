-- Prove2me | Theorems.Thm_Printed_abs_term_le
-- name    : Printed.abs_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:19.909841+00:00
-- url     : https://prove2.me/theorems/c332b6f6-8705-4270-921c-8a48525dc20c
-- title:
--   Printed: abs term le
-- statement:
--   «each a product of at most g² values»: each value is below 2^B, so a term of the display is at
--   most (2^B − 1)^{g²} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L211-L236
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L211-L236

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

theorem Printed.abs_term_le (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) {z : Fin g → List Bool} (hz : z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) :
    |(∏ a with Paper.grouping hK0 x a = γ, N.W a (z a)) *
        (∏ p ∈ pairs (Fin g) with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ p : Fin g × Fin g with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2)| ≤ (2 ^ B - 1) ^ g ^ 2 := by sorry
