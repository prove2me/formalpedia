-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_maDens_one
-- name    : ReciprocityTheory.AnForm.maDens_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:06.643514+00:00
-- url     : https://prove2.me/theorems/29fc5949-240a-5351-85d2-653f25f1fabb
-- title:
--   An Form: ma Dens one
-- statement:
--   The An Form construction uses the ma Dens one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L14-L19

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

theorem ReciprocityTheory.AnForm.maDens_one (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) :
    maDens φ z = 2 / Real.pi * levi (φ 0) z (Pi.single 0 1) := by sorry
