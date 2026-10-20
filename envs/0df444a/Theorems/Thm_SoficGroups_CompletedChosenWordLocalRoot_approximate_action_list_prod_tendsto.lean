-- Prove2me | Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_approximate_action_list_prod_tendsto
-- name    : SoficGroups.CompletedChosenWordLocalRoot.approximate_action_list_prod_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/85423565-de17-4d22-a552-320366640f82
-- title:
--   SoficGroups.CompletedChosenWordLocalRoot.approximate_action_list_prod_tendsto
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators

theorem SoficGroups.CompletedChosenWordLocalRoot.approximate_action_list_prod_tendsto
    {G : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (l : List G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (p n l.prod) ((l.map (p n)).prod))
      atTop (nhds 0) := by sorry
