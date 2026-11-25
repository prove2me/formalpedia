-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67
-- name    : P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:14.297957+00:00
-- url     : https://prove2.me/theorems/6bc406f4-9440-47e7-8f7e-ea1c3566d4e2
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Covolume period Gram cast Add 5c2e72ba1c67: P2 M Ground Theory Heights  Heights Cusp Covolume period Gram cast Add 5c2e72ba1c67
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Covolume period Gram cast Add 5c2e72ba1c67 construction uses the P2 M Ground Theory Heights  Heights Cusp Covolume period Gram cast Add 5c2e72ba1c67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCovolume.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCovolume.lean#L15-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCovolume
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
open GroundTheory.Heights₂.Heights.CuspCovolume

theorem P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67 {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    periodGram τ (Fin.castAdd g k) (Fin.castAdd g k) = (τ.map Complex.im)⁻¹ k k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspCovolume».«periodGram_castAdd» := P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67
