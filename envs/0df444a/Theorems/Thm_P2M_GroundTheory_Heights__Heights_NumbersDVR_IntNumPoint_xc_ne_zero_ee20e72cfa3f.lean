-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:14.2858+00:00
-- url     : https://prove2.me/theorems/c1badad3-e40b-41d3-a712-4c79b8832a1c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point xc ne zero ee20e72cfa3f: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point xc ne zero ee20e72cfa3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point xc ne zero ee20e72cfa3f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point xc ne zero ee20e72cfa3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L94-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f {p : Σ k, ι k} (hp : (X p : MRing ι F) ∉ V) : xc V p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«xc_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f
