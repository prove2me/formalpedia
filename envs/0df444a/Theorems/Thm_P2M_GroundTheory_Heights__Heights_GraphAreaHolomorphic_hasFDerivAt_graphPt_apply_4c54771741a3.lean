-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:43.637136+00:00
-- url     : https://prove2.me/theorems/bcc285a5-90e4-554d-8d71-42c550b9fc7c
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic has FDeriv At graph Pt apply 4c54771741a3: P2 M Ground Theory Heights  Heights Graph Area Holomorphic has FDeriv At graph Pt apply 4c54771741
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic has FDeriv At graph Pt apply 4c54771741a3 construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic has FDeriv At graph Pt apply 4c54771741a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L69-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L69-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3 {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    {L : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin m)} (hF : HasFDerivAt F L x)
    {T : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)} (hG : HasFDerivAt (graphPt e F) T x)
    (v : EuclideanSpace ℂ (Fin d)) :
    T v = WithLp.toLp 2 (fun j => Sum.elim (fun i => v i) (fun i => L v i) (e j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«hasFDerivAt_graphPt_apply» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3
