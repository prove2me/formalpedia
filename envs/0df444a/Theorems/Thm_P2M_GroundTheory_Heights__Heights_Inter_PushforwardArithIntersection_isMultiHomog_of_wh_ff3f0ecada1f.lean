-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:13.019374+00:00
-- url     : https://prove2.me/theorems/0bd8dec7-4ade-4091-a741-5318fd93de82
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog of wh ff3f0ecada1f: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog of w
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog of wh ff3f0ecada1f construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog of wh ff3f0ecada1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L22-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«isMultiHomog_of_wh» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_of_wh_ff3f0ecada1f
