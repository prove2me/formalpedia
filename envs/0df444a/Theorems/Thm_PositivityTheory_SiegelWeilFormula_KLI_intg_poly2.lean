-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_poly2
-- name    : PositivityTheory.SiegelWeilFormula.KLI.intg_poly2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:20.085124+00:00
-- url     : https://prove2.me/theorems/9b7638eb-b514-492b-9537-7f366f3b32a2
-- title:
--   KLI: intg poly2
-- statement:
--   The KLI construction uses the intg poly2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean#L53-L61

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

theorem PositivityTheory.SiegelWeilFormula.KLI.intg_poly2 {b : ℂ} (hb : b.re < 0) (l μ : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) := by sorry
