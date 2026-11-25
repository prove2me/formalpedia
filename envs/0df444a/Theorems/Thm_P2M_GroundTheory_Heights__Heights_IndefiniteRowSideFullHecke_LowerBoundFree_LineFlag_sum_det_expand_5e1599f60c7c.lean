-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:17.363357+00:00
-- url     : https://prove2.me/theorems/ddc71b14-f9fb-47b0-a0e2-136664f98f05
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag sum det expand 5e1599f60c7c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Boun
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag sum det expand 5e1599f60c7c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Line Flag sum det expand 5e1599f60c7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/FlagLine.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/FlagLine.lean#L124-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ q : Fin 2 → Fin 2, (∏ a, g (q a) a) * (detInt q : ℂ) = g.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«LineFlag».«sum_det_expand» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c
