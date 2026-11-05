-- Prove2me | Theorems.Thm_Value_edge_unique
-- name    : Value.edge_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:46.810251+00:00
-- url     : https://prove2.me/theorems/7d648ec3-c09f-4834-806c-44b3ec37fde0
-- title:
--   Value: edge unique
-- statement:
--   One edge of the clique of the groups, given by the group indices G, G' (in either order): for
--   every choice of one string t(a, b) of c_{a,b} bits per pair (a, b), a in group G, b in group G',
--   exactly one string of L bits has these strings in its blocks and zeros after the last block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L119-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L119-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Value.edge_unique (Nq : PNet C) (hK0 : 0 < K) (c : C) (x L : ℕ) (G G' : Fin K) (hle : lbLen K g Nq c x G G' ≤ L) (t : Fin g × Fin g → List Bool)
    (ht : ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → (t q).length = Nq.cap c q.1 q.2) :
    ∃! w : List Bool, w ∈ mD K g Nq c x L G G' ∧ ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → mdec K g Nq c x G G' w q = t q := by sorry
