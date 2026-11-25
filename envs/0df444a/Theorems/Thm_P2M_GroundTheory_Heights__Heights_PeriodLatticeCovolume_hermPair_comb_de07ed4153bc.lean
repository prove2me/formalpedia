-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc
-- name    : P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:29.075918+00:00
-- url     : https://prove2.me/theorems/b5393775-efb4-4fc6-b4d5-5ddcc301cef1
-- title:
--   P2 M Ground Theory Heights  Heights Period Lattice Covolume herm Pair comb de07ed4153bc: P2 M Ground Theory Heights  Heights Period Lattice Covolume herm Pair comb de07ed4153bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Lattice Covolume herm Pair comb de07ed4153bc construction uses the P2 M Ground Theory Heights  Heights Period Lattice Covolume herm Pair comb de07ed4153bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodLatticeCovolume.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPeriodLatticeCovolume.lean#L15-L26

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

theorem P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℝ) (b : Fin m → ι → ℂ)
    (x y : Fin m → ℝ) :
    hermPair A (∑ a, (x a : ℂ) • b a) (∑ c, (y c : ℂ) • b c) =
      ∑ a, ∑ c, x a * y c * hermPair A (b a) (b c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodLatticeCovolume».«hermPair_comb» := P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc
