-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:53.258122+00:00
-- url     : https://prove2.me/theorems/799bd120-0687-50f1-b5b1-01c332118991
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Vertical Div unif ff6fcf4a766b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Vert
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Vertical Div unif ff6fcf4a766b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Vertical Div unif ff6fcf4a766b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemOfMemSupportDivCycle.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemOfMemSupportDivCycle.lean#L165-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b (ϖ : O) {P : Ideal (MRingOver O ι)} (hP : P.IsPrime) :
    IsVerticalDiv ϖ P 0 (C ϖ) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«isVerticalDiv_unif» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b
