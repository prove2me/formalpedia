-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_variation_le_relation_difference
-- name    : SoficGroups.KunThomFiberCoarea.firstMultiplicity_variation_le_relation_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/3072b5f3-1a41-4dcb-8b39-4f08700ce33b
-- title:
--   SoficGroups.KunThomFiberCoarea.firstMultiplicity_variation_le_relation_difference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.firstMultiplicity_variation_le_relation_difference
    {V : Type*} [Fintype V] [DecidableEq V]
    (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (firstMultiplicity U x)
      (firstMultiplicity W x)) ≤
        (U \ W).card + (W \ U).card := by sorry
