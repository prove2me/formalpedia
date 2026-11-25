-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:53.034058+00:00
-- url     : https://prove2.me/theorems/5a7a4234-3c57-5ee5-94a3-f892035ddde5
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume unip Radical le vec Fix Group d0154db07684: P2 M Ground Theory Heights  Heights Finite Covolume unip Radical le vec Fix Group d0154db07684
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume unip Radical le vec Fix Group d0154db07684 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume unip Radical le vec Fix Group d0154db07684 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsStabilizerLevi.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsStabilizerLevi.lean#L60-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684 (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    unipRadical h v x₀ ≤ vecFixGroup h v x₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«unipRadical_le_vecFixGroup» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
