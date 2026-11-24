-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:58.35626+00:00
-- url     : https://prove2.me/theorems/0d55f261-3d44-4e99-89a5-9b22094d667f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Bundles i Sub apply a90d421cce72: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Bundles
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Bundles i Sub apply a90d421cce72 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR Bundles i Sub apply a90d421cce72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ScaledRankOneLeStandardRankOne.lean#L588-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ScaledRankOneLeStandardRankOne.lean#L588-L589

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72 (v : Fin 1 → Ω) (j : Fin 2) : iSub v j = if j = 0 then v 0 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«Bundles».«iSub_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
