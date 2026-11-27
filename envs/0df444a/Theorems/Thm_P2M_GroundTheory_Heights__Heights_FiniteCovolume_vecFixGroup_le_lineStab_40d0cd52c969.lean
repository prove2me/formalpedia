-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecFixGroup_le_lineStab_40d0cd52c969
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecFixGroup_le_lineStab_40d0cd52c969
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:32.909236+00:00
-- url     : https://prove2.me/theorems/0559abaa-f953-4aef-af03-52001cba55d8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume vec Fix Group le line Stab 40d0cd52c969: P2 M Ground Theory Heights  Heights Finite Covolume vec Fix Group le line Stab 40d0cd52c969
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume vec Fix Group le line Stab 40d0cd52c969 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume vec Fix Group le line Stab 40d0cd52c969 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsLineStabHaar.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsLineStabHaar.lean#L55-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecFixGroup_le_lineStab_40d0cd52c969 (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    vecFixGroup h v x₀ ≤ lineStab h v x₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«vecFixGroup_le_lineStab» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecFixGroup_le_lineStab_40d0cd52c969
