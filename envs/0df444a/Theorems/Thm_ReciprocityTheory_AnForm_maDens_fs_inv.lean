-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_maDens_fs_inv
-- name    : ReciprocityTheory.AnForm.maDens_fs_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:43.821103+00:00
-- url     : https://prove2.me/theorems/85729831-430c-4308-a1a3-b52aa34f7afd
-- title:
--   An Form: ma Dens fs inv
-- statement:
--   The An Form construction uses the ma Dens fs inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L98-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L98-L128

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.maDens_fs_inv (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) (hz : z 0 ≠ 0)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖(y 0)⁻¹‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by sorry
