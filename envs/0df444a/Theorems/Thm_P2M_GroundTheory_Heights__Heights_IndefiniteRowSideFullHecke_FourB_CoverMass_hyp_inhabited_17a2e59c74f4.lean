-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_CoverMass_hyp_inhabited_17a2e59c74f4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_CoverMass_hyp_inhabited_17a2e59c74f4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:19.360164+00:00
-- url     : https://prove2.me/theorems/0c8be901-c555-5f2f-9a1c-7b1b0f1b567c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Cover Mass hyp inhabited 17a2e59c74f4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Cover Mass hy
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Cover Mass hyp inhabited 17a2e59c74f4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Cover Mass hyp inhabited 17a2e59c74f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L139-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L139-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_CoverMass_hyp_inhabited_17a2e59c74f4 :
    CoverMass.Hyp (Set.univ : Set (Fin 1 → ℂ)) ∅ id 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«CoverMass».«hyp_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_CoverMass_hyp_inhabited_17a2e59c74f4
