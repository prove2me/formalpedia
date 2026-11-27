-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_hyp_inhabited_092cb4eec4d5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_hyp_inhabited_092cb4eec4d5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:20.190466+00:00
-- url     : https://prove2.me/theorems/2a857b71-6722-547f-bd48-7e50970c8549
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext hyp inhabited 092cb4eec4d5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext hyp inhabited 092cb4eec4d5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext hyp inhabited 092cb4eec4d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L154-L164

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_hyp_inhabited_092cb4eec4d5 :
    RiemannExt.Hyp (Polynomial ℂ) (Polynomial.X * Polynomial.X) Polynomial.X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«RiemannExt».«hyp_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_hyp_inhabited_092cb4eec4d5
