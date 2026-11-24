-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:24.200856+00:00
-- url     : https://prove2.me/theorems/ef25bdaf-e95f-472d-90c8-f49fcfae3b6f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval eq zero of mem 938035ac7e4d: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval eq ze
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval eq zero of mem 938035ac7e4d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval eq zero of mem 938035ac7e4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L22-L32

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d {z : (Σ k, ι k) → Φ} {f : MRing ι O} (hf : f ∈ pointIdeal O z) :
    aeval z f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«aeval_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_eq_zero_of_mem_938035ac7e4d
