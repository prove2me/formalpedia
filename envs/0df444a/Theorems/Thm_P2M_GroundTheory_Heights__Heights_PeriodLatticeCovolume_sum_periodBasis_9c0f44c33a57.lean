-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57
-- name    : P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:26.513857+00:00
-- url     : https://prove2.me/theorems/6a275711-e85b-4736-8ac2-5f3ca6af18e8
-- title:
--   P2 M Ground Theory Heights  Heights Period Lattice Covolume sum period Basis 9c0f44c33a57: P2 M Ground Theory Heights  Heights Period Lattice Covolume sum period Basis 9c0f44c33a57
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Lattice Covolume sum period Basis 9c0f44c33a57 construction uses the P2 M Ground Theory Heights  Heights Period Lattice Covolume sum period Basis 9c0f44c33a57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodLatticeCovolume.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodLatticeCovolume.lean#L28-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodLatticeCovolume
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
open GroundTheory.Heights₂.Heights.PeriodLatticeCovolume

theorem P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57 {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    ∑ i, ((Fin.append a n i : ℤ) : ℂ) • periodBasis τ i = intVecC a + τ *ᵥ intVecC n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodLatticeCovolume».«sum_periodBasis» := P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_sum_periodBasis_9c0f44c33a57
