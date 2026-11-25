-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:16.297394+00:00
-- url     : https://prove2.me/theorems/5dc279e0-ef31-4551-b15e-5752d7057ed8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Model Over line c8d82f335840: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Model
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Model Over line c8d82f335840 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Model Over line c8d82f335840 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemOfMemSupportDivCycle.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemOfMemSupportDivCycle.lean#L175-L181

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
variable (O)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840 : IsModelOver (⊥ : Ideal (MRingOver O (fun _ : Unit => Fin 2))) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«isModelOver_line» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840
