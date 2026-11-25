-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_evX_temperate
-- name    : PositivityTheory.SiegelWeilFormula.KFock.evX_temperate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:54.084297+00:00
-- url     : https://prove2.me/theorems/63f82c64-a140-4e4d-89fb-7529864d07c0
-- title:
--   KFock: ev X temperate
-- statement:
--   The KFock construction uses the ev X temperate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/EvXTemperate.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/EvXTemperate.lean#L29-L46

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock

theorem PositivityTheory.SiegelWeilFormula.KFock.evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => evX P x) := by sorry
