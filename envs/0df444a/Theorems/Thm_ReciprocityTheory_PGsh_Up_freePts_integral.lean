-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_freePts_integral
-- name    : ReciprocityTheory.PGsh.Up.freePts_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:45.163949+00:00
-- url     : https://prove2.me/theorems/6d072bff-085b-46bc-a664-6b8595a9c862
-- title:
--   Up: free Pts integral
-- statement:
--   The Up construction uses the free Pts integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsUnitMinor.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsUnitMinor.lean#L13-L26

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
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

theorem ReciprocityTheory.PGsh.Up.freePts_integral {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) {w : Fin n × Fin h → C} (hw : w ∈ F.pts)
    (y : Fin n × Fin h) : v (w y) ≤ 1 := by sorry
