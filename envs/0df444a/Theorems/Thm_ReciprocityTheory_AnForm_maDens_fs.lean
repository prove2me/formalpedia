-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_maDens_fs
-- name    : ReciprocityTheory.AnForm.maDens_fs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:03.265915+00:00
-- url     : https://prove2.me/theorems/204b2400-121b-4d0e-be62-ac34478bb7ab
-- title:
--   An Form: ma Dens fs
-- statement:
--   The An Form construction uses the ma Dens fs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L71-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L71-L96

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

theorem ReciprocityTheory.AnForm.maDens_fs (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖y 0‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by sorry
