-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_apply
-- name    : ReciprocityTheory.PGsh.Up.sumLat_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:07.846458+00:00
-- url     : https://prove2.me/theorems/d44e774d-818c-4d15-b051-74819795cff6
-- title:
--   Up: sum Lat apply
-- statement:
--   The Up construction uses the sum Lat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L19-L22

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

theorem ReciprocityTheory.PGsh.Up.sumLat_apply {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by sorry
