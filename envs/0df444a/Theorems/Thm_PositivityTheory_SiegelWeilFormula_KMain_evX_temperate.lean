-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KMain_evX_temperate
-- name    : PositivityTheory.SiegelWeilFormula.KMain.evX_temperate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:40.621799+00:00
-- url     : https://prove2.me/theorems/4fcfa3ac-41e4-4858-934d-29761450b30b
-- title:
--   KMain: ev X temperate
-- statement:
--   The KMain construction uses the ev X temperate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSchwartzSums/SchwartzPolyGauss.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSchwartzSums/SchwartzPolyGauss.lean#L30-L44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
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
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KMain
open PositivityTheory.Rg.Sw

theorem PositivityTheory.SiegelWeilFormula.KMain.evX_temperate {m n : ℕ} (P : PX m n) : Function.HasTemperateGrowth (fun x => evX P x) := by sorry
