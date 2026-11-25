-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f
-- name    : P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:24.936526+00:00
-- url     : https://prove2.me/theorems/4d0568b7-d070-4a9c-9709-b03f841df0c2
-- title:
--   P2 M Ground Theory Heights  Heights MCGram Entry Deriv triple 84a0c6a2690f: P2 M Ground Theory Heights  Heights MCGram Entry Deriv triple 84a0c6a2690f
-- statement:
--   The P2 M Ground Theory Heights  Heights MCGram Entry Deriv triple 84a0c6a2690f construction uses the P2 M Ground Theory Heights  Heights MCGram Entry Deriv triple 84a0c6a2690f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramEntryDeriv.lean#L25-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f {u v w : E → ℂ} {p : E} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) (hw : DifferentiableAt ℝ w p) :
    DifferentiableAt ℝ (fun q => u q * v q * w q) p ∧
      ‖fderiv ℝ (fun q => u q * v q * w q) p‖ ≤
        ‖fderiv ℝ u p‖ * ‖v p‖ * ‖w p‖ + ‖u p‖ * ‖fderiv ℝ v p‖ * ‖w p‖ +
          ‖u p‖ * ‖v p‖ * ‖fderiv ℝ w p‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCGramEntryDeriv».«triple» := P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f
