-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KMain_coordX_temperate
-- name    : PositivityTheory.SiegelWeilFormula.KMain.coordX_temperate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:30.509847+00:00
-- url     : https://prove2.me/theorems/657aeb9a-c711-491f-a44b-e4830792520a
-- title:
--   KMain: coord X temperate
-- statement:
--   The KMain construction uses the coord X temperate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSchwartzSums/SchwartzPolyGauss.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSchwartzSums/SchwartzPolyGauss.lean#L15-L28

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

theorem PositivityTheory.SiegelWeilFormula.KMain.coordX_temperate {m n : ℕ} (k : Fin m × Fin n × Bool) : Function.HasTemperateGrowth (coordX k) := by sorry
