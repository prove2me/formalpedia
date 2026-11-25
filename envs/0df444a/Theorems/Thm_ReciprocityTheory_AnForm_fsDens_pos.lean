-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_fsDens_pos
-- name    : ReciprocityTheory.AnForm.fsDens_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:05.75132+00:00
-- url     : https://prove2.me/theorems/c1b3ada7-51f0-5bf2-acdb-801ae6eef390
-- title:
--   An Form: fs Dens pos
-- statement:
--   The An Form construction uses the fs Dens pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L11-L12

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

theorem ReciprocityTheory.AnForm.fsDens_pos (z : ℂ) : 0 < fsDens z := by sorry
