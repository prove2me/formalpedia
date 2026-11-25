-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd
-- name    : P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:39.199218+00:00
-- url     : https://prove2.me/theorems/93bfca90-4853-411f-842f-5d233fe70fe2
-- title:
--   P2 M Ground Theory Heights  Heights Leading Covolume period Basis of lt 3607769c3abd: P2 M Ground Theory Heights  Heights Leading Covolume period Basis of lt 3607769c3abd
-- statement:
--   The P2 M Ground Theory Heights  Heights Leading Covolume period Basis of lt 3607769c3abd construction uses the P2 M Ground Theory Heights  Heights Leading Covolume period Basis of lt 3607769c3abd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLeadingCovolume.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLeadingCovolume.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLeadingCovolume
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
open GroundTheory.Heights₂.Heights.LeadingCovolume

theorem P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : ℕ) (hi : i < g)
    (hi' : i < g + g) : periodBasis τ ⟨i, hi'⟩ = Pi.single (⟨i, hi⟩ : Fin g) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadingCovolume».«periodBasis_of_lt» := P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd
