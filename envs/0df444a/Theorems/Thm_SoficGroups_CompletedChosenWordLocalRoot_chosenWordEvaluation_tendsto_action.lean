-- Prove2me | Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_chosenWordEvaluation_tendsto_action
-- name    : SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_tendsto_action
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/709aede8-fdd1-4a85-ab21-5a50fdea9482
-- title:
--   SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_tendsto_action
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

theorem SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_tendsto_action
    {G ι : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g : G, ((w g).map s).prod = g)
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (σ n i) (p n (s i)))
        atTop (nhds 0))
    (g : G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (chosenWordEvaluation (σ n) w g) (p n g))
      atTop (nhds 0) := by sorry
