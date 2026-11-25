-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_eval_toMv
-- name    : PositivityTheory.SiegelWeilFormula.KLI.eval_toMv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:01.828233+00:00
-- url     : https://prove2.me/theorems/778c890e-d02b-468c-9bd6-59f2d2c24547
-- title:
--   KLI: eval to Mv
-- statement:
--   The KLI construction uses the eval to Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L12-L13

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

theorem PositivityTheory.SiegelWeilFormula.KLI.eval_toMv {σ : Type} (i : σ) (p : Polynomial ℂ) (g : σ → ℂ) : eval g (toMv i p) = p.eval (g i) := by sorry
