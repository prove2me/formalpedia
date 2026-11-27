-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_volume_isAddHaar
-- name    : PositivityTheory.SiegelWeilFormula.KFock.volume_isAddHaar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:35.410983+00:00
-- url     : https://prove2.me/theorems/90f57bf5-5ac4-565a-8010-398c3c1b472e
-- title:
--   KFock: volume is Add Haar
-- statement:
--   The KFock construction uses the volume is Add Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean#L9-L12

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock

theorem PositivityTheory.SiegelWeilFormula.KFock.volume_isAddHaar (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by sorry
