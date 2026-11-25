-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_hypotheses_met_aa36e8267b1e
-- name    : P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_hypotheses_met_aa36e8267b1e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:48.235505+00:00
-- url     : https://prove2.me/theorems/b6b784b5-48d1-45fe-ba62-46ec3fc7e043
-- title:
--   P2 M Ground Theory Heights  Heights Log Det Gram Deriv hypotheses met aa36e8267b1e: P2 M Ground Theory Heights  Heights Log Det Gram Deriv hypotheses met aa36e8267b1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Det Gram Deriv hypotheses met aa36e8267b1e construction uses the P2 M Ground Theory Heights  Heights Log Det Gram Deriv hypotheses met aa36e8267b1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L100-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_hypotheses_met_aa36e8267b1e :
    (1 : ℝ) ≤ ((1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).map
      (fun x : ℝ => (x : ℂ)) * (1 : Matrix (Fin 1) (Fin 1) ℂ)).det.re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogDetGramDeriv».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_hypotheses_met_aa36e8267b1e
