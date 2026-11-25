-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_deg_toMv
-- name    : PositivityTheory.SiegelWeilFormula.KLI.deg_toMv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:56.841694+00:00
-- url     : https://prove2.me/theorems/5d2d558d-4648-4c54-8d33-e7f93a4258f3
-- title:
--   KLI: deg to Mv
-- statement:
--   The KLI construction uses the deg to Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L15-L22

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI

theorem PositivityTheory.SiegelWeilFormula.KLI.deg_toMv {σ : Type} (i : σ) (p : Polynomial ℂ) : (toMv i p).totalDegree ≤ p.natDegree := by sorry
