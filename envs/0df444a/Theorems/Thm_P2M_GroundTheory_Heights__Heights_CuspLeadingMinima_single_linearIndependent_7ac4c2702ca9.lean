-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9
-- name    : P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:16.49985+00:00
-- url     : https://prove2.me/theorems/416f56ef-5ae0-4288-b552-e6254aeb72d8
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Leading Minima single linear Independent 7ac4c2702ca9: P2 M Ground Theory Heights  Heights Cusp Leading Minima single linear Independent 7ac4c2702ca9
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Leading Minima single linear Independent 7ac4c2702ca9 construction uses the P2 M Ground Theory Heights  Heights Cusp Leading Minima single linear Independent 7ac4c2702ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspLeadingMinima.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima
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
open GroundTheory.Heights₂.Heights.CuspLeadingMinima

theorem P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9 {g r : ℕ} (h : r ≤ g) :
    LinearIndependent ℤ (fun j : Fin r => (Pi.single (Fin.castLE h j) (1 : ℂ) : Fin g → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspLeadingMinima».«single_linearIndependent» := P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9
