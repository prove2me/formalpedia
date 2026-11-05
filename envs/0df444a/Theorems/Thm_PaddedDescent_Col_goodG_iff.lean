-- Prove2me | Theorems.Thm_PaddedDescent_Col_goodG_iff
-- name    : PaddedDescent.Col.goodG_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:14:29.064228+00:00
-- url     : https://prove2.me/theorems/c94ed5a2-623a-4488-bad8-e868bfba17fa
-- title:
--   Col: good G iff
-- statement:
--   What the test says: every class has fewer than 2g/K nodes, and two classes share at most β label
--   bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Good.lean#L33-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Good.lean#L33-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Colouring
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_Col_Good
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.Col
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F Finset
variable {C : Type}
variable {K g : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

theorem PaddedDescent.Col.goodG_iff (hK : 0 < K) (hN : Np.Presents c N t S) (β x : ℕ) :
    goodG K g Np β (c, x) = true ↔ (∀ G : Fin K, K * #{a : Fin g | chi hK x a = G} < 2 * g) ∧
      ∀ G G' : Fin K, G ≠ G' → (N.merge (chi hK x) [] []).c G G' ≤ β := by sorry
