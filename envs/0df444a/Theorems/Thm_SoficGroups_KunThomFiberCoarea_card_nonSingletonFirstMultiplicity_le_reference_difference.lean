-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonFirstMultiplicity_le_reference_difference
-- name    : SoficGroups.KunThomFiberCoarea.card_nonSingletonFirstMultiplicity_le_reference_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/912b975e-ef1c-48dd-b6a0-c1cf9c2a9579
-- title:
--   SoficGroups.KunThomFiberCoarea.card_nonSingletonFirstMultiplicity_le_reference_difference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.card_nonSingletonFirstMultiplicity_le_reference_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V) :
    (Finset.univ.filter fun x : V =>
      firstMultiplicity U x ≠ 1).card ≤
        (U \ SoficGroups.permutationGraph p).card +
          (SoficGroups.permutationGraph p \ U).card := by sorry
