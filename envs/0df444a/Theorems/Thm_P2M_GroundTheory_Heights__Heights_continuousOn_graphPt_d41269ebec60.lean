-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuousOn_graphPt_d41269ebec60
-- name    : P2M_GroundTheory_Heights__Heights_continuousOn_graphPt_d41269ebec60
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:11.456698+00:00
-- url     : https://prove2.me/theorems/7d5fe713-a287-4a44-b109-a16b69ee7614
-- title:
--   P2 M Ground Theory Heights  Heights continuous On graph Pt d41269ebec60: P2 M Ground Theory Heights  Heights continuous On graph Pt d41269ebec60
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous On graph Pt d41269ebec60 construction uses the P2 M Ground Theory Heights  Heights continuous On graph Pt d41269ebec60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L28-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_continuousOn_graphPt_d41269ebec60 {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)} {Ω : Set (EuclideanSpace ℂ (Fin d))}
    (hF : ContinuousOn F Ω) : ContinuousOn (graphPt e F) Ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuousOn_graphPt» := P2M_GroundTheory_Heights__Heights_continuousOn_graphPt_d41269ebec60
