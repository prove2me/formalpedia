-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:39.371122+00:00
-- url     : https://prove2.me/theorems/197f0b16-df0e-4b4c-ab91-15bd4d81317c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor vdeg add 4f8428746a98: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor vdeg add 4f8428746a98
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor vdeg add 4f8428746a98 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor vdeg add 4f8428746a98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L97-L99

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98 (α β : K → ℕ) : vdeg (α + β) = vdeg α + vdeg β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«vdeg_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
