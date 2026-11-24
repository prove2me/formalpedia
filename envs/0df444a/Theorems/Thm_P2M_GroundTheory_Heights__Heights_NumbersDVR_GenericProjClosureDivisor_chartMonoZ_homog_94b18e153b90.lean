-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:52.353907+00:00
-- url     : https://prove2.me/theorems/88b91384-c502-4d55-aa66-8dcd55f8ffea
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart Mono Z homog 94b18e153b90: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart Mono Z
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart Mono Z homog 94b18e153b90 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor chart Mono Z homog 94b18e153b90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L105-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L105-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90 (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMonoZ O M M' c α) (vdeg α) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«chartMonoZ_homog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
