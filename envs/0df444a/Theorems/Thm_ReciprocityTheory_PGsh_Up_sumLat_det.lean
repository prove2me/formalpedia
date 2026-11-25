-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_det
-- name    : ReciprocityTheory.PGsh.Up.sumLat_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:30.574829+00:00
-- url     : https://prove2.me/theorems/344a5f62-83f0-463d-af88-40bd44e4dc88
-- title:
--   Up: sum Lat det
-- statement:
--   The Up construction uses the sum Lat det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L24-L28

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.sumLat_det {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) :
    (sumLat Mτ).B.det = ∏ τ, (Mτ τ).B.det := by sorry
