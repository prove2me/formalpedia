-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_degC_eq_card_projPts_8b835b054292
-- name    : P2M_GroundTheory_Heights__Heights_degC_eq_card_projPts_8b835b054292
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:46:01.357534+00:00
-- url     : https://prove2.me/theorems/4815049e-d7c2-4c6b-9a0b-f1f6788bc733
-- title:
--   P2 M Ground Theory Heights  Heights deg C eq card proj Pts 8b835b054292: P2 M Ground Theory Heights  Heights deg C eq card proj Pts 8b835b054292
-- statement:
--   The P2 M Ground Theory Heights  Heights deg C eq card proj Pts 8b835b054292 construction uses the P2 M Ground Theory Heights  Heights deg C eq card proj Pts 8b835b054292 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPtsIntegralPoints.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPtsIntegralPoints.lean#L14-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G

theorem P2M_GroundTheory_Heights__Heights_degC_eq_card_projPts_8b835b054292 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) : Geo.degC P = Nat.card (projPts P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«degC_eq_card_projPts» := P2M_GroundTheory_Heights__Heights_degC_eq_card_projPts_8b835b054292
