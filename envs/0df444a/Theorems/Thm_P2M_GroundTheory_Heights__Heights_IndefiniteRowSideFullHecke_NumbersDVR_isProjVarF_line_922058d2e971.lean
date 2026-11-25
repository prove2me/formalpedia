-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isProjVarF_line_922058d2e971
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isProjVarF_line_922058d2e971
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:27.544038+00:00
-- url     : https://prove2.me/theorems/5e85d124-3d63-4557-86a5-5966cb0c7c28
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Proj Var F line 922058d2e971: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Proj V
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Proj Var F line 922058d2e971 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR is Proj Var F line 922058d2e971 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L299-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L299-L304

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
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
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isProjVarF_line_922058d2e971 (F : Type*) [Field F] :
    IsProjVarF (⊥ : Ideal (MRingOver F (fun _ : Unit => Fin 2))) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«isProjVarF_line» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isProjVarF_line_922058d2e971
