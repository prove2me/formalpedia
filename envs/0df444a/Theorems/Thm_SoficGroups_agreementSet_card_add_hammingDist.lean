-- Prove2me | Theorems.Thm_SoficGroups_agreementSet_card_add_hammingDist
-- name    : SoficGroups.agreementSet_card_add_hammingDist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/735fd73e-d5d0-4af0-913d-e41a9d36bea3
-- title:
--   SoficGroups.agreementSet_card_add_hammingDist
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.agreementSet_card_add_hammingDist {V : Type*}
    [Fintype V] [DecidableEq V] (c c' : Equiv.Perm V) :
    (agreementSet c c').card +
      hammingDist (fun x => c x) (fun x => c' x) = Fintype.card V := by sorry
