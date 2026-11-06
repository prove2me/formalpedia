-- Prove2me | Theorems.Thm_Printed_run_clique_within
-- name    : Printed.run_clique_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:30:15.333208+00:00
-- url     : https://prove2.me/theorems/beb5b9b5-e59d-4a2e-8ceb-e17f3ecfac00
-- title:
--   Printed: run clique within
-- statement:
--   **Running the algorithm for (K, e) with L, B' in the roles of λ, B, and answering each query by
--   computing the entry**: for a good grouping number x, the machine M, given (L, B'), with its queries
--   answered by `tableQ`, outputs the value of the network within T_M·(E + 2) operations, where T_M ≤
--   C·2^{eK²L}(B' + L)^C and
--   E = c₁·2^{P⌊2g/K⌋}·τ is the cost of one entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L129-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L129-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.run_clique_within (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc c₁ : ℕ} (hK0 : 0 < K) (hg : 0 < g) (hM : AchievedBy M Cc K e)
    {N : Net g} {P B τ x : ℕ} (hN : N.Is P B) (hgood : Good N.c P (Paper.grouping hK0 x))
    (hE : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * Paper.groupedLength K g N.U P),
      (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K (Paper.groupedLength K g N.U P) (γ.val, Θ)) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (c₁ * (P + B) ^ c₁)
        ((Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ) ∧
      |(Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ| < 2 ^ bitsOut K g P B) :
    ∃ TM : ℕ, (QueryMachine.mapIn (fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))))
        (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked)))).Within (netOracle N) (fun _ => τ) (netInput N P B, x)
          (TM * (c₁ * 2 ^ (P * (2 * g / K)) * τ + 2))
          (size (netInput N P B, x) + Cc * (bitsOut K g P B + Paper.groupedLength K g N.U P) ^ Cc + c₁ * (P + B) ^ c₁ + 1) N.value ∧
      (TM : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((bitsOut K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ Cc := by sorry
