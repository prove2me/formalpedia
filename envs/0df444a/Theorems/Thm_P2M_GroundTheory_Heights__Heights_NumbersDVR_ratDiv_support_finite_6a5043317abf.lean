-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_support_finite_6a5043317abf
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_support_finite_6a5043317abf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:05.933066+00:00
-- url     : https://prove2.me/theorems/c2be43d1-69a8-48d5-b0b7-ee7fe2758423
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rat Div support finite 6a5043317abf: P2 M Ground Theory Heights  Heights Numbers DVR rat Div support finite 6a5043317abf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rat Div support finite 6a5043317abf construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rat Div support finite 6a5043317abf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorsCommute.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorsCommute.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_support_finite_6a5043317abf (h4 : DivCycleFiniteSupport.Statement.{u}) {O : Type u} [CommRing O]
    [IsNoetherianRing O] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) : (Function.support (ratDiv P f g)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ratDiv_support_finite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_support_finite_6a5043317abf
