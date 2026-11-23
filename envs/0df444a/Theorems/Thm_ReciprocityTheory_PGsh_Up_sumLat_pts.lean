-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_sumLat_pts
-- name    : ReciprocityTheory.PGsh.Up.sumLat_pts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:40.772859+00:00
-- url     : https://prove2.me/theorems/1f194b66-dfd4-4de8-bea3-007d662349af
-- title:
--   Up: sum Lat pts
-- statement:
--   The Up construction uses the sum Lat pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthSqBlockVandermonde.lean#L39-L51

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

theorem ReciprocityTheory.PGsh.Up.sumLat_pts {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by sorry
